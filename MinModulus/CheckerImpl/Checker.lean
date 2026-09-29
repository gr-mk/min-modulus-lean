import MinModulus.CheckerImpl.TauDP
import MinModulus.CheckerImpl.Enum
import MinModulus.CheckerImpl.Primes
/-
# `MinModulus.CheckerImpl.Checker` — the global run and the checked Bool

Status: complete, no `sorry`. Core Lean only. **No closed expensive constants in this
module** (it is precompiled; a closed constant would be evaluated whenever it is imported):
the run is the function `run P`, the Bool is `checkWith P`; `check := checkWith fullParams`
lives in the non-precompiled module `MinModulus.CheckerImpl.Certificate`.

## What `run P` computes (all values are P-values, i.e. numerators over `2^62`)
Let `X = P.PMAX`. For each prime `p ≤ PX` (increasing, from `primesUpTo PX`):
* if `δ_p = 0`: `cost p = firstMoment m p (primes < p)` ≥ `E[U_p(s)]` (requires `δ_q = 0` for
  all `q < p`; checked, flag `ok`);
* else the **comparison bound** `cost p = comparisonCost …` ≥ `E[(U_p(s) − δ_p)^+]/(1 − δ_p)`,
  using the A/B split at `z = z_p`, the enumeration of `s_A ≤ X_p`, the τ_A DP (`AState`) and the
  τ_B DP over the primes in `(z_p, p)` (`BState`, maintained incrementally).
* then `ET2 *= fac2 p δ_p`, `ET25 *= fac25 p δ_p`, `ET3 *= fac3 p δ_p` (running upper bounds of
  `E[τ^θ]` and, for θ = 2, of `T = Π (1 + ν_q(3q−1)/(q−1)^2)`).
For `PX < p ≤ X`: blocks `[B_i, B_{i+1})`, `B_0 = PX + 1`, `B_{i+1} = min(B_i + max 1 (B_i >>> s), X+1)`.
With `n_i = countUnmarked (sieve X) B_i B_{i+1}` (≥ number of primes in the block) and
`dn = deltaN P B_i` (δ is constant on the block; for `fullParams` it is `4092/10000` for all
`p ≥ 50000`): `ET_θ *= fac_θ(B_i, dn)^{n_i}` and the **per-prime cost of every prime in the block**
is `blocks[i].val = blockVal B_i dn ET2 ET25 ET3` (with the updated `ET_θ`, which bound
`E[τ(s)^θ]` for every prime of the block); the block contributes `n_i · blocks[i].val`.

## The certificate data (see `Certificate.lean`)
* `δ₀ p = deltaCert P p` (`= deltaN P p / 10^9` for `p ≤ X`, `1/2` for `p > X`);
* `c₀ p = costOf r P p / 2^62` (`r = run P`);
* `T₀ = r.T / 2^62`;
* `checkWith P = true` means `r.ok` and `r.etaA + r.etaB + r.etaC + ⌈r.T·100/(189 X)⌉ < 2^62`, where
  `r.etaA + r.etaB = Σ_{p ≤ PX prime} costOf r P p` and `r.etaC = Σ_i blocks[i].count · blocks[i].val`.
-/
namespace MinModulus.CheckerImpl

/-- `(J, M1, M2, p^{J−1}, p^{J−2})` for the prime `p`: `M_j = ⌈m/p^j⌉`, `J` = least `j ≥ 1` with
`M_j = 1`. `J = 4` means "not supported" (then the run fails). -/
def thresholds (m p : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let M1 := cdiv m p
  let M2 := cdiv m (p * p)
  let M3 := cdiv m (p * p * p)
  if M1 ≤ 1 then (1, 1, 1, 1, 0)
  else if M2 ≤ 1 then (2, M1, 1, p, 1)
  else if M3 ≤ 1 then (3, M1, M2, p * p, p)
  else (4, M1, M2, p * p, p)

/-- Pattern data for the A-primes `aps` with δ-values `adns`: `bits[i] = 2^k` if `aps[i]` is the
`k`-th tilted prime (`adns[i] > 0`), else `0`; for each pattern `pat < 2^(#tilted)`,
`cup[pat] ≥ 2^62·C[pat] ≥ clo[pat]` with
`C[pat] = Π_{untilted q} (q−1)/q · Π_{tilted, bit clear} (1 − ν_q/q) · Π_{tilted, bit set} ν_q(q−1)/q`,
`ν_q = 10^9/(10^9 − dn_q)`. -/
def patternConsts (aps adns : Array Nat) : Array Nat × Array Nat × Array Nat :=
  let (bits, nt) := mkBits 0 0 #[] aps.size
  let npat := 1 <<< nt
  let (cup, clo) := mkC bits 0 #[] #[] npat
  (bits, cup, clo)
where
  mkBits (i nt : Nat) (bits : Array Nat) : Nat → Array Nat × Nat
    | 0 => (bits, nt)
    | f + 1 => if adns[i]! == 0 then mkBits (i + 1) nt (bits.push 0) f
               else mkBits (i + 1) (nt + 1) (bits.push (1 <<< nt)) f
  /-- exact numerator and denominator of `C[pat]` -/
  numDen (bits : Array Nat) (pat i num den : Nat) : Nat → Nat × Nat
    | 0 => (num, den)
    | f + 1 =>
      let q := aps[i]!
      let d := adns[i]!
      if d == 0 then numDen bits pat (i + 1) (num * (q - 1)) (den * q) f
      else
        let nd := DDEN - d
        if pat &&& bits[i]! != 0 then numDen bits pat (i + 1) (num * (DDEN * (q - 1))) (den * (q * nd)) f
        else numDen bits pat (i + 1) (num * (q * nd - DDEN)) (den * (q * nd)) f
  mkC (bits : Array Nat) (pat : Nat) (cup clo : Array Nat) : Nat → Array Nat × Array Nat
    | 0 => (cup, clo)
    | f + 1 =>
      let (num, den) := numDen bits pat 0 1 1 aps.size
      mkC bits (pat + 1) (cup.push (ratUp num den)) (clo.push (ratDn num den)) f

/-- Enumeration cut-off `X_p = max(10^4, ⌊XC · M^(XE2/2)⌋)`, `M = ⌈m/p⌉`
(`⌊XC·M^(XE2/2)⌋ = ⌊√(XC²·M^XE2)⌋`). Any value is valid. -/
def enumCutoff (P : Params) (p : Nat) : Nat :=
  max 10000 (Nat.sqrt (P.XC * P.XC * cdiv P.m p ^ P.XE2))

/-- `Σ_{i < a.size} i · a[i]` (exact). -/
def weightedSum (a : Array Nat) : Nat := go 0 0 a.size
where go (i acc : Nat) : Nat → Nat
  | 0 => acc
  | f + 1 => go (i + 1) (acc + i * a[i]!) f

/-- `Σ a[i]` (exact). -/
def arrSum (a : Array Nat) : Nat := a.foldl (· + ·) 0

/-- Output of the comparison bound at one prime. -/
structure CmpOut where
  cost : Nat
  ok : Bool
  nleaf : Nat

/-- **Comparison bound** at a prime `p` with `δ_p = dn/10^9 > 0`, `t = δ_p`:
upper P-value of `E[(U_p(s) − t)^+]/(1 − t)`, using
`U_p(s) ≤ U_A(s_A) + (τ(s_B) − 1)·τ(s_A)/(p−1)` (`s_A` = part over the A-primes `aps`, `s_B` = part
over the primes in `(z, p)`, whose law is in `B`), hence
`E[(U_p − t)^+] ≤ Σ_{s_A ≤ X_p} P(s_A)·G(τ(s_A), U_A(s_A)) + Σ_k R_k·G(k, k/(p−1)) + E[τ_A;lost]·E[τ_B]/(p−1)`
with `G(k, u) = E_B[(u + (τ_B − 1)k/(p−1) − t)^+]` and `R_k ≥ P(τ_A = k, kept, s_A > X_p)`.
* linear case `u ≥ t`: `G = u − t + (E[τ_B] − 1)·k/(p−1)` (exact identity);
* FB case `u < t`: `G = (k/(p−1))·FB(1 + (t − u)(p−1)/k)` (`gUp`).
`A` must be `buildA aps adns KMAX`; `B.D.size` must exceed `⌊t(p−1)⌋ + 2`. -/
def comparisonCost (P : Params) (p dn : Nat) (aps adns : Array Nat) (A : AState) (B : BState) :
    CmpOut :=
  let (J, M1, M2, pj1, pj2) := thresholds P.m p
  let uDen := pj1 * (p - 1)
  let It := cdiv (dn * uDen) DDEN
  let n1max := cdiv It pj1 + 1
  -- prefix tables of the B law, for ⌊c⌋ ≤ K (c ≤ 1 + t(p−1))
  let K := dn * (p - 1) / DDEN + 2
  let okK := K < B.D.size
  let (S0, PP) := fbTable B.D K
  let fb := fun cP => fbUp B.EB B.lost S0 PP cP
  -- enumeration of s_A ≤ X_p
  let (bits, cup, clo) := patternConsts aps adns
  let cfg : EnumCfg := { aps, bits, X := enumCutoff P p, M1, M2, pj1, pj2, It, n1max, cup, clo,
                         kmax := P.KMAX }
  let acc := runEnum cfg M1
  -- linear leaves: Σ P·(u − t) + (E[τ_B] − 1)·Σ P·τ/(p−1)
  let SP := arrSum acc.hn
  let SN := weightedSum acc.hn
  let S1 := weightedSum acc.hs1
  let S2 := weightedSum acc.hs2
  let SPI := pj1 * SN + pj2 * S1 + S2 - pj2 * S2
  let lin1 := cdiv (SPI * DDEN - dn * uDen * SP) (DDEN * uDen)
  let lin2 := cdiv ((B.EB - ONE) * (SN + S1)) ((p - 1) * ONE)
  -- FB leaves, aggregated by (n1, σ1, σ2)
  let fbsum := fbLeaves fb cfg uDen acc.fb 0 0 acc.fb.size
  -- remaining s_A > X_p (and τ_A ≤ KMAX, kept): R_k = up[k] − pen[k]
  let (rs0, rs1, remfb) := remaining fb uDen A.up acc.pen 1 0 0 0 (min P.KMAX A.kTop)
  let remlin := cdiv (B.EB * rs1) ((p - 1) * ONE) - dn * rs0 / DDEN
  -- lost part of τ_A
  let tailPart := cdiv (A.tailA * B.EB) ((p - 1) * ONE)
  let total := lin1 + lin2 + fbsum + remlin + remfb + tailPart
  { cost := cdiv (total * DDEN) (DDEN - dn)
    ok := acc.ok && okK && J ≤ 3 && enumCutoff P p ≤ ONE
    nleaf := acc.nleaf }
where
  /-- `Σ_{idx} fbArr[idx] · G(τ, I/uDen)` over nonzero entries, `idx = (n1·M1 + σ1)·M2 + σ2`. -/
  fbLeaves (fb : Nat → Nat) (cfg : EnumCfg) (uDen : Nat) (fbArr : Array Nat) (idx acc : Nat) :
      Nat → Nat
    | 0 => acc
    | f + 1 =>
      let w := fbArr[idx]!
      if w == 0 then fbLeaves fb cfg uDen fbArr (idx + 1) acc f
      else
        let σ2 := idx % cfg.M2
        let σ1 := (idx / cfg.M2) % cfg.M1
        let n1 := idx / (cfg.M2 * cfg.M1)
        let I := cfg.pj1 * n1 + cfg.pj2 * (σ1 - σ2) + σ2
        let g := gUp fb dn p (n1 + σ1) I uDen
        fbLeaves fb cfg uDen fbArr (idx + 1) (acc + mulUp w g) f
  /-- remaining mass by `k`: linear (`k/(p−1) ≥ t`) → `(Σ R_k, Σ k R_k)`; else `Σ R_k·G(k, k/(p−1))`. -/
  remaining (fb : Nat → Nat) (uDen : Nat) (up pen : Array Nat) (k rs0 rs1 remfb : Nat) :
      Nat → Nat × Nat × Nat
    | 0 => (rs0, rs1, remfb)
    | f + 1 =>
      let R := up[k]! - getD0 pen k
      if R == 0 then remaining fb uDen up pen (k + 1) rs0 rs1 remfb f
      else if dn * (p - 1) ≤ k * DDEN then
        remaining fb uDen up pen (k + 1) (rs0 + R) (rs1 + k * R) remfb f
      else
        remaining fb uDen up pen (k + 1) rs0 rs1 (remfb + mulUp R (gUp fb dn p k k (p - 1))) f

/-- State of the loop over the primes `p ≤ PX`.

**Invariant** after `primeLoop P primes dns st0 0 k` (primes with index `< k` processed), with
`cost_j` the value computed by `stepPrime` for `p_j = primes[j]`:
* `etaA = Σ_{j<k, p_j < PD} cost_j`, `etaB = Σ_{j<k, p_j ≥ PD} cost_j`, `costs[p_j] = cost_j` for
  `j < k` and `costs[n] = 0` for every other `n`;
* `ET2 ≥ 2^62·Π_{j<k} fac2(p_j)/2^62` etc. (each product rounded up with `mulUp`), hence
  `ET_θ/2^62 ≥ E[τ(s)^θ]` for `s` over the processed primes, every cap;
* `B` is the B-part DP (`BState`) of the primes with index in `[bLo, bHi)` (any processing
  order), `bHi ≤ k`; when `p_k` is processed by the comparison bound, first
  `bLo = zIdx = nAz(p_k)` and `bHi = k`, i.e. `B` = the primes in `(z, p_k)`;
* if `aValid`, `A = buildA primes[0:zIdx] dns[0:zIdx] KMAX`;
* `allZero` ⇔ `dns[j] = 0` for all `j < k`; `ok` is the conjunction of all run-time guards. -/
structure LoopSt where
  etaA : Nat
  etaB : Nat
  ET2 : Nat
  ET25 : Nat
  ET3 : Nat
  B : BState
  /-- the B part contains exactly the primes with index in `[bLo, bHi)`. -/
  bLo : Nat
  bHi : Nat
  A : AState
  /-- `A` was built for the primes with index `< zIdx` (valid iff `aValid`). -/
  zIdx : Nat
  aValid : Bool
  /-- all primes processed so far have `δ = 0`. -/
  allZero : Bool
  ok : Bool
  /-- `costs[p]` = cost of the prime `p ≤ PX` (0 elsewhere). -/
  costs : Array Nat
  nleaf : Nat

/-- Adds the primes with index in `[i, i + fuel)` to the B part. -/
def addToB (primes dns : Array Nat) (B : BState) (i : Nat) : Nat → BState
  | 0 => B
  | f + 1 => addToB primes dns (B.addPrime primes[i]! dns[i]!) (i + 1) f

/-- Number of A-primes for `p = primes[k]`: the length of the longest prefix of `primes[0:k]`
with `q ≤ Z0` and `q < ⌈m/p⌉` (so `z` = the last of them, or `z = 1` if none). -/
def numAPrimes (primes : Array Nat) (k Z0 M : Nat) : Nat := go 0 k
where go (j : Nat) : Nat → Nat
  | 0 => j
  | f + 1 => let q := primes[j]!; if q ≤ Z0 && q < M then go (j + 1) f else j

/-- One step of the loop: the prime `p = primes[k]`. -/
def stepPrime (P : Params) (primes dns : Array Nat) (st : LoopSt) (k : Nat) : LoopSt :=
  let p := primes[k]!
  let dn := dns[k]!
  let (cost, st) :=
    if dn == 0 then
      (firstMoment P.m p (primes.extract 0 k), { st with ok := st.ok && st.allZero })
    else
      let nAz := numAPrimes primes k P.Z0 (cdiv P.m p)
      -- (re)build the A part if z changed; B keeps the primes in (z, p)
      let st :=
        if st.aValid && nAz == st.zIdx then st
        else
          let bEmpty := st.bLo == st.bHi
          let okz := bEmpty || nAz ≤ st.bLo
          let (B, bLo, bHi) :=
            if bEmpty then (st.B, nAz, nAz)
            else (addToB primes dns st.B nAz (st.bLo - nAz), nAz, st.bHi)
          { st with B, bLo, bHi, ok := st.ok && okz, zIdx := nAz, aValid := true,
                    A := buildA (primes.extract 0 nAz) (dns.extract 0 nAz) P.KMAX }
      let st := { st with B := addToB primes dns st.B st.bHi (k - st.bHi), bHi := k }
      let out := comparisonCost P p dn (primes.extract 0 nAz) (dns.extract 0 nAz) st.A st.B
      (out.cost, { st with ok := st.ok && out.ok, nleaf := st.nleaf + out.nleaf })
  match st with
  | ⟨etaA, etaB, ET2, ET25, ET3, B, bLo, bHi, A, zIdx, aValid, allZero, ok, costs, nleaf⟩ =>
    ⟨if p < P.PD then etaA + cost else etaA, if p < P.PD then etaB else etaB + cost,
     mulUp ET2 (fac2 p dn), mulUp ET25 (fac25 p dn), mulUp ET3 (fac3 p dn),
     B, bLo, bHi, A, zIdx, aValid, allZero && dn == 0, ok, costs.set! p cost, nleaf⟩

/-- Loop over the prime indices `[k, k + fuel)`. -/
def primeLoop (P : Params) (primes dns : Array Nat) (st : LoopSt) (k : Nat) : Nat → LoopSt
  | 0 => st
  | f + 1 => primeLoop P primes dns (stepPrime P primes dns st k) (k + 1) f

/-- One block `[start, stop)` of primes `> PX`: `count` = unmarked numbers in it (≥ number of
primes in it), `val` = per-prime cost (P-value) of every prime in it. -/
structure BlockRec where
  start : Nat
  stop : Nat
  count : Nat
  val : Nat

/-- State of the block loop (`PX < p ≤ X`). -/
structure BlkSt where
  etaC : Nat
  ET2 : Nat
  ET25 : Nat
  ET3 : Nat
  blocks : Array BlockRec

/-- Block loop starting at `B` (processes blocks while `B ≤ X`). Block `[B, E)` with
`E = min(B + max 1 (B >>> blockShift), X + 1)`; δ on the block is `deltaN P B`. -/
def blockLoop (P : Params) (sv : ByteArray) (st : BlkSt) (B : Nat) : Nat → BlkSt
  | 0 => st
  | f + 1 =>
    if P.PMAX < B then st
    else
      let E := min (B + max 1 (B >>> P.blockShift)) (P.PMAX + 1)
      let n := countUnmarked sv B E
      let dn := deltaN P B
      let ET2 := mulUp st.ET2 (powUp (fac2 B dn) n)
      let ET25 := mulUp st.ET25 (powUp (fac25 B dn) n)
      let ET3 := mulUp st.ET3 (powUp (fac3 B dn) n)
      let v := blockVal B dn ET2 ET25 ET3
      blockLoop P sv { etaC := st.etaC + n * v, ET2, ET25, ET3,
                       blocks := st.blocks.push ⟨B, E, n, v⟩ } E f

/-- Result of a run (all P-values). -/
structure Result where
  /-- `Σ cost p` over primes `p < PD` -/
  etaA : Nat
  /-- `Σ cost p` over primes `PD ≤ p ≤ PX` -/
  etaB : Nat
  /-- `Σ_i blocks[i].count · blocks[i].val` (blocks, `PX < p ≤ X`) -/
  etaC : Nat
  /-- upper P-value of `T = Π_{q ≤ X prime} (1 + ν_q (3q−1)/(q−1)^2)` -/
  T : Nat
  /-- upper P-values of `E[τ^{5/2}]`, `E[τ^3]` over all primes `≤ X` (diagnostics) -/
  ET25 : Nat
  ET3 : Nat
  ok : Bool
  /-- `costs[p]` for primes `p ≤ PX` -/
  costs : Array Nat
  /-- the blocks covering `(PX, X]`, in increasing order -/
  blocks : Array BlockRec
  nleaf : Nat

/-- **The global run.** -/
def run (P : Params) : Result :=
  let primes := primesUpTo P.PX
  let dns := primes.map (deltaN P)
  -- size of the B-part arrays: every ⌊c⌋ + 1 is below N (c ≤ 1 + δ_p (p−1))
  let N := primes.foldl (fun a p => max a ((deltaN P p) * (p - 1) / DDEN)) 0 + 4
  let st0 : LoopSt :=
    { etaA := 0, etaB := 0, ET2 := ONE, ET25 := ONE, ET3 := ONE, B := BState.init N,
      bLo := 0, bHi := 0, A := ⟨#[], #[], ONE, 0, 0⟩, zIdx := 0, aValid := false,
      allZero := true, ok := true, costs := Array.replicate (P.PX + 1) 0, nleaf := 0 }
  let st := primeLoop P primes dns st0 0 primes.size
  let sv := sieve P.PMAX
  let bs := blockLoop P sv ⟨0, st.ET2, st.ET25, st.ET3, #[]⟩ (P.PX + 1) (P.PMAX + 1)
  { etaA := st.etaA, etaB := st.etaB, etaC := bs.etaC, T := bs.ET2, ET25 := bs.ET25, ET3 := bs.ET3,
    ok := st.ok, costs := st.costs, blocks := bs.blocks, nleaf := st.nleaf }

/-- Upper P-value of the tail term `T · 100/(189 X)`. -/
def tailUp (P : Params) (T : Nat) : Nat := cdiv (T * 100) (189 * P.PMAX)

/-- `η_up = etaA + etaB + etaC` plus the tail term. -/
def Result.total (r : Result) (P : Params) : Nat := r.etaA + r.etaB + r.etaC + tailUp P r.T

/-- The per-prime cost `c₀ p` (P-value) of the run `r`: `costs[p]` for `p ≤ PX`; for `p > PX` the
`val` of the block `[start, stop)` containing `p` (found by `Array.find?`; `0` if none). -/
def costOf (r : Result) (P : Params) (p : Nat) : Nat :=
  if p ≤ P.PX then r.costs.getD p 0
  else match r.blocks.find? (fun b => b.start ≤ p && p < b.stop) with
    | some b => b.val
    | none => 0

/-- The checked Bool: the run succeeded and `Σ_p c₀ p + T₀·100/(189 X) < 1` in the form
`etaA + etaB + etaC + ⌈T·100/(189 X)⌉ < 2^62`. -/
def checkWith (P : Params) : Bool :=
  let r := run P
  r.ok && decide (r.total P < ONE)

/-- What the checked Bool means (the starting point of the "Bool → real inequality" lemma). -/
theorem checkWith_spec {P : Params} (h : checkWith P = true) :
    (run P).ok = true ∧ (run P).total P < ONE := by
  unfold checkWith at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

end MinModulus.CheckerImpl
