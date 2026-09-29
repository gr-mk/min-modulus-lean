import MinModulus.Checker2Impl.SBH
import MinModulus.Checker2Impl.TauSplit
import MinModulus.CheckerImpl.Primes
/-
# `MinModulus.Checker2Impl.Checker` — the global run of the second checker and the checked Bool

Status: complete, no `sorry`. Core Lean only. **No closed expensive constants in this module**
(it is precompiled): the run is the function `run2 P`, the Bool is `checkWith2 P`; the certificate
`check2` lives in the non-precompiled module `MinModulus.Checker2Impl.Certificate`.

## What `run2 P` computes (P-values, numerators over `2^62`)
Primes `p ≤ PX` in increasing order (`primesUpTo PX`, exact trial division), `dn = deltaN2 P p`:
* `dn = 0` (then all smaller primes have `dn = 0`, flag `allZero`):
  `cost = firstMoment m p (primes below p)` (`CheckerImpl.firstMoment`, `= E[U_p]`);
* `N1 = ⌈m/p⌉ ≥ 3`: `H` is extended to `primes[iN1:k]` (`HState.extend`) and
  `cost = (sbhCost P p dn primes dns k H).cost`;
* `N1 ≤ 2`: on first use the `τ_s` law is frozen (`TauSState.freeze`), and
  `cost = splitCost m NN p dn tb el`;
* then `T ← mulUp T (fac2 p dn)` (the tail product `∏ (1 + ν_q(3q−1)/(q−1)²)`), and `p` is added
  to the `τ_s` law if `N1 ≥ 3` (`p < YS`), else to the e-law.
For `PX < p ≤ X`: blocks `[B, E)`, `B₀ = PX + 1`, `E = min (B + max 1 (B >>> blockShift)) (X + 1)`;
every number of the block left unmarked by `sieve X` (every prime is) is added to the e-law with the
constant δ-value `dC = deltaN2 P (PX + 1)`; then `val = splitCost m NN B dC tb el` (threshold and
divisor at `B`), `etaC += count·val`, `T ← mulUp T (powUp (fac2 B dC) count)`.

## Certificate data (see `Certificate.lean`)
`δ₀ p = deltaCert2 P p`; `c₀ p = costOf2 r P p / 2^62`; `T₀ = r.T / 2^62`;
`checkWith2 P = true` means `r.ok` and `etaA + etaB + etaC + ⌈T·100/(189 X)⌉ < 2^62`
(exactly the hypothesis shape of `CheckerMath.cert_of_check`).

## Run-time guards (flag `ok`)
`allZero` for the first-moment primes; the S/B/H guards (`y² ≥ N1`, `y ≥ N2`, the `H` indices,
`⌊c_b⌋ ≤ K`, DFS fuel); the δ schedule is constant beyond the last knot and `kps[last] ≤ PX`;
`2 ≤ NN`; `m ≤ PX` (so `N1 = 1` in the block phase); the τ-split primes are `≥ 3`.
-/
namespace MinModulus.Checker2Impl

open MinModulus.CheckerImpl

/-- State of the loop over the primes `p ≤ PX`. -/
structure LoopSt2 where
  etaA : Nat
  etaB : Nat
  T : Nat
  H : HState
  tauS : TauSState
  tb : Option TauSTab
  el : ELaw
  allZero : Bool
  ok : Bool
  costs : Array Nat
  nleaf : Nat
  npat : Nat
  nprof : Nat

/-- One step of the loop: the prime `p = primes[k]`. -/
def stepPrime2 (P : Params2) (primes dns : Array Nat) (st : LoopSt2) (k : Nat) : LoopSt2 :=
  let p := primes[k]!
  let dn := dns[k]!
  let N1 := cdiv P.m p
  let st :=
    if dn == 0 then
      let cost := firstMoment P.m p (primes.extract 0 k)
      { st with etaA := st.etaA + cost, costs := st.costs.set! p cost,
                ok := st.ok && st.allZero }
    else if 3 ≤ N1 then
      let iN1 := min (countLt primes N1) k
      let (H, okH) := st.H.extend primes dns P.KH iN1 k
      let out := sbhCost P p dn primes dns k H
      { st with etaB := st.etaB + out.cost, costs := st.costs.set! p out.cost, H,
                ok := st.ok && okH && out.ok, nleaf := st.nleaf + out.nleaf,
                npat := st.npat + out.npat, nprof := st.nprof + out.nprof }
    else
      let tb := match st.tb with
        | some tb => tb
        | none => st.tauS.freeze P.TS
      let cost := splitCost P.m P.NN p dn tb st.el
      { st with etaB := st.etaB + cost, costs := st.costs.set! p cost, tb := some tb,
                ok := st.ok && decide (3 ≤ p) }
  let T := mulUp st.T (fac2 p dn)
  if 3 ≤ N1 then
    { st with T, tauS := st.tauS.add P.TS p dn, allZero := st.allZero && dn == 0 }
  else
    { st with T, el := st.el.add P.NN p dn, allZero := st.allZero && dn == 0 }

/-- Loop over the prime indices `[k, k + fuel)`. -/
def primeLoop2 (P : Params2) (primes dns : Array Nat) (st : LoopSt2) (k : Nat) : Nat → LoopSt2
  | 0 => st
  | f + 1 => primeLoop2 P primes dns (stepPrime2 P primes dns st k) (k + 1) f

/-- One block `[start, stop)` of numbers `> PX`: `count` = unmarked numbers in it (`≥` the number
of primes in it), `val` = per-prime cost (P-value) of every prime in it. -/
structure BlockRec2 where
  start : Nat
  stop : Nat
  count : Nat
  val : Nat
  deriving Inhabited

/-- Adds every number `n ∈ [i, i + fuel)` with `sv[n] = 0` to the e-law (δ-value `dC`); returns the
new law and the number of such `n`. -/
def addUnmarked (sv : ByteArray) (NN dC : Nat) (el : ELaw) (cnt i : Nat) : Nat → ELaw × Nat
  | 0 => (el, cnt)
  | f + 1 =>
    if sv.get! i == 0 then addUnmarked sv NN dC (el.add NN i dC) (cnt + 1) (i + 1) f
    else addUnmarked sv NN dC el cnt (i + 1) f

/-- State of the block loop. -/
structure BlkSt2 where
  etaC : Nat
  T : Nat
  el : ELaw
  blocks : Array BlockRec2

/-- Block loop starting at `B` (while `B ≤ X`). -/
def blockLoop2 (P : Params2) (sv : ByteArray) (tb : TauSTab) (dC : Nat) (st : BlkSt2) (B : Nat) :
    Nat → BlkSt2
  | 0 => st
  | f + 1 =>
    if P.X < B then st
    else
      let E := min (B + max 1 (B >>> P.blockShift)) (P.X + 1)
      let (el, n) := addUnmarked sv P.NN dC st.el 0 B (E - B)
      let v := splitCost P.m P.NN B dC tb el
      blockLoop2 P sv tb dC
        { etaC := st.etaC + n * v, T := mulUp st.T (powUp (fac2 B dC) n), el,
          blocks := st.blocks.push ⟨B, E, n, v⟩ } E f

/-- Result of a run (all P-values). -/
structure Result2 where
  /-- `Σ cost p` over the primes `p < PD` (first moment) -/
  etaA : Nat
  /-- `Σ cost p` over the primes `PD ≤ p ≤ PX` -/
  etaB : Nat
  /-- `Σ_i blocks[i].count · blocks[i].val` (`PX < p ≤ X`) -/
  etaC : Nat
  /-- upper P-value of `T = ∏_{q ≤ X prime} (1 + ν_q (3q−1)/(q−1)²)` -/
  T : Nat
  ok : Bool
  costs : Array Nat
  blocks : Array BlockRec2
  nleaf : Nat
  npat : Nat
  nprof : Nat

/-- The δ schedule is constant beyond the last knot, which must be `≤ PX`; `dC` is that value. -/
def schedOk (P : Params2) : Bool :=
  P.kps.size != 0 && P.kps.size == P.kds.size && decide (P.kps[P.kps.size - 1]! ≤ P.PX) &&
    decide (P.PD ≤ P.PX)

/-- **The global run.** -/
def run2 (P : Params2) : Result2 :=
  let primes := primesUpTo P.PX
  let dns := primes.map (deltaN2 P)
  let st0 : LoopSt2 :=
    { etaA := 0, etaB := 0, T := ONE, H := HState.init P.KH, tauS := TauSState.init P.TS,
      tb := none, el := ELaw.init P.NN, allZero := true, ok := true,
      costs := zeros (P.PX + 1), nleaf := 0, npat := 0, nprof := 0 }
  let st := primeLoop2 P primes dns st0 0 primes.size
  let tb := match st.tb with
    | some tb => tb
    | none => st.tauS.freeze P.TS
  let dC := deltaN2 P (P.PX + 1)
  let sv := sieve P.X
  let bs := blockLoop2 P sv tb dC ⟨0, st.T, st.el, #[]⟩ (P.PX + 1) (P.X + 1)
  { etaA := st.etaA, etaB := st.etaB, etaC := bs.etaC, T := bs.T,
    ok := st.ok && schedOk P && decide (2 ≤ P.NN) && decide (P.m ≤ P.PX) && decide (0 < dC)
      && decide (2 ^ 27 ≤ P.X) && decide (P.PX ≤ P.X),
    costs := st.costs, blocks := bs.blocks, nleaf := st.nleaf, npat := st.npat,
    nprof := st.nprof }

/-- Upper P-value of the tail term `T · 100/(189 X)`. -/
def tailUp2 (P : Params2) (T : Nat) : Nat := cdiv (T * 100) (189 * P.X)

/-- `η_up = etaA + etaB + etaC` plus the tail term. -/
def Result2.total (r : Result2) (P : Params2) : Nat := r.etaA + r.etaB + r.etaC + tailUp2 P r.T

/-- The per-prime cost `c₀ p` (P-value) of the run `r`: `costs[p]` for `p ≤ PX`; for `p > PX` the
`val` of the block `[start, stop)` containing `p` (`0` if none). -/
def costOf2 (r : Result2) (P : Params2) (p : Nat) : Nat :=
  if p ≤ P.PX then r.costs.getD p 0
  else match r.blocks.find? (fun b => b.start ≤ p && p < b.stop) with
    | some b => b.val
    | none => 0

/-- The checked Bool: the run succeeded and `Σ_p c₀ p + T₀·100/(189 X) < 1`, in the form
`etaA + etaB + etaC + ⌈T·100/(189 X)⌉ < 2^62`. -/
def checkWith2 (P : Params2) : Bool :=
  let r := run2 P
  r.ok && decide (r.total P < ONE)

/-- What the checked Bool means. -/
theorem checkWith2_spec {P : Params2} (h : checkWith2 P = true) :
    (run2 P).ok = true ∧ (run2 P).total P < ONE := by
  unfold checkWith2 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

end MinModulus.Checker2Impl
