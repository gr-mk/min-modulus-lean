import MinModulus.Checker2Impl.Laws
/-
# `MinModulus.Checker2Impl.SBH` — the exact S/B/H bound with lower-tail tables (`N1 = ⌈m/p⌉ ≥ 3`)

Status: complete, no `sorry`. Core Lean only.

## The mathematics (math layer: `Checker2Math/Identities.lean`)
Fix a prime `p`, `t = δ_p = dn/10^9`, `N1 = ⌈m/p⌉` (`d < N1 ↔ d·p < m`), `N2 = ⌈m/p²⌉`, and a split
point `y` with `y² ≥ N1` and `y ≥ N2` (checked at run time). Split the primes `q < p` into
`S = {q < y}`, `B = {y ≤ q < N1}`, `H = {q ≥ max y N1}`. With `c(d) = 1 − p^{1−j0(d)}`:
```
(p − 1)·U_p(s) = τ(s_S)·T − F(s_S) − (1 − 1/p)·b          (S/B/H identity, exact)
T = ∏_{q ∈ B ∪ H} (v_q + 1),  F(n) = Σ_{d ∣ n, d < N1} c(d),  b = Σ_{q ∈ B, v_q ≥ 1} a_q(s_S),
a_q(n) = #{d ∣ n : d·q < N1}.
```
For a fixed `s_S` (a DFS leaf, `τ = τ(s_S)`) and `β(b) = t(p−1) + F + ω b` (`ω = 1 − 1/p`), the
**lower-tail identity** `x⁺ = x + (−x)⁺` gives, exactly,
```
E_{B,H}[(τT − β(b))⁺] = τ E[T] − t(p−1) − F − ω E[b] + τ Σ_b Σ_{k ≤ c_b} (c_b − k) P(T = k, b),
c_b = β(b)/τ,
```
so only the joint law of `(T, b)` restricted to `T ≤ ⌊c_b⌋ ≤ ⌊t(p−1)⌋ + 1 + b` is needed: **no lost
mass, no exponent cut** (a path with `T ≤ K` has every `v_q + 1 ≤ K`). `E[T] = E[T_H]·∏_B E[v+1]` and
`E[b] = Σ_B a_q ν_q/q` are closed forms. Every threshold is replaced by a *lower* bound
(`β` decreases the hinge), consistently in both places.

`F` and the profile `(a_q)_{q∈B}` depend only on the divisors of `s_S` below `N1`, i.e. on the
**small pattern** `π_j = min(v_j, kk_j)` (`kk_j` = largest `k` with `q_j^k < N1`), enumerated in
mixed radix (`smallDivs`). Profiles are deduplicated (`findIdx?`); one lower-tail table per profile.

## Two fixed-point scales
Probabilities (and the laws, `S0`) are **P-values** `x/2^62`. Quantities of size `≥ 1` that enter
the per-leaf arithmetic (`F`, `β`, `c_b`, `S1`, `E[T]`, `E[b]`, leaf values, the DFS bounds and
sums) are **W-values** `x/2^48` (`W48 = 2^48`), so that the hot loop stays below `2^63` (unboxed
machine words; a `Nat` above `2^63` is a GMP number). `mulUp x y = ⌈x·y/2^62⌉` maps
(P-value, W-value) to a W-value; conversions: `W ← P` is `cdiv · 2^14` (up) or `· >>> 14` (down),
`P ← W` is `· <<< 14` (exact).

## The code
* `HState`: the law of `T_H` on `[0, KH]` (full steps, `lawStepFull`) and `E[T_H]` (P-value), for the
  primes `primes[lo:hi]`; maintained incrementally by `HState.extend` (H only grows).
* `patternData`: `patF[π]` (lower W-value of `F`), `patProf[π]` (profile index), `profs`.
* `buildTab`: rows `b = 0 … bm` of the `(T, b)` law on `[0, K]`, `K = min KH (⌊t(p−1)⌋ + 2 + bm)`,
  started from the `T_H` law, one `rowsStep` per `B` prime, then prefix tables per row
  (`S0` P-values, `S1W` = lower W-values of `Σ_{j ≤ k} j·D[j]`), and `EbW` (lower W-value of `E[b]`).
* `dfsNode`/`dfsExp`: DFS over the exponents of `S` (increasing primes, exponents `0, 1, …`).
  A subtree `{v_j ≥ a, deeper free}` is **pruned** when `a > acut_j` or its bound
  `P·τ·h_j(a)·∏_{i>j} E[v_i+1]·E[T]` (which bounds `E[τ_S T; subtree] ≥ E[(τ_S T − β)⁺; subtree]`)
  is `< epsAbs`; the bound is then added to `prune`. Leaves add `mulUp P (leafValue …)`.
* `sbhCost`: `cdiv (((leaf + prune) <<< 14)·10^9) ((p−1)(10^9 − dn))`, an upper P-value of
  `E[(U_p − t)⁺]/(1 − t)`.
All run-time guards go into the flag `ok`.
-/
namespace MinModulus.Checker2Impl

open MinModulus.CheckerImpl

/-- `2^48`, the unit of W-values (not inlined). -/
@[noinline] def W48 : Nat := 281474976710656
theorem W48_eq : W48 = 2 ^ 48 := by decide

/-! ## Thresholds, `c(d)`, small patterns -/

/-- `j0(d) − 1`, where `j0(d)` is the least `j ≥ 1` with `d·p^j ≥ m` (for `p ≥ 2`, `d ≥ 1`, and
`m ≤ 2^64`; fuel 64). -/
def j0m1 (m p d : Nat) : Nat := go (d * p) 0 64
where
  go (x j : Nat) : Nat → Nat
    | 0 => j
    | f + 1 => if x < m then go (x * p) (j + 1) f else j

/-- Lower W-value of `c(d) = 1 − p^{1 − j0(d)}`. -/
def cdLoW (m p d : Nat) : Nat := W48 - cdiv W48 (p ^ j0m1 m p d)

/-- `#[cdLoW m p 0, …, cdLoW m p (N1 − 1)]` (entry 0 is unused). -/
def cdTable (m p N1 : Nat) : Array Nat := go 0 N1 (Array.emptyWithCapacity N1)
where
  go (d : Nat) : Nat → Array Nat → Array Nat
    | 0, acc => acc
    | f + 1, acc => go (d + 1) f (acc.push (cdLoW m p d))

/-- The largest `k` with `q^k < N1` (for `q ≥ 2`). -/
def kkOf (q N1 : Nat) : Nat := go 0 q 64
where
  go (k qk : Nat) : Nat → Nat
    | 0 => k
    | f + 1 => if qk < N1 then go (k + 1) (qk * q) f else k

/-- Pushes `x·q, x·q², …` (at most `fuel` values) while they are `< N1`. -/
def powsBelow (N1 q : Nat) (acc : Array Nat) (x : Nat) : Nat → Array Nat
  | 0 => acc
  | f + 1 => if x * q < N1 then powsBelow N1 q (acc.push (x * q)) (x * q) f else acc

/-- The divisors below `N1` of `∏_j Sq[j]^{e_j}`, where `e_j` are the mixed-radix digits of `pat`
(radix `kk[j] + 1`); without repetition, starting with `1` (requires `1 < N1`). -/
def smallDivs (Sq kk : Array Nat) (N1 pat : Nat) : Array Nat := go 0 pat #[1] Sq.size
where
  go (j r : Nat) (ds : Array Nat) : Nat → Array Nat
    | 0 => ds
    | f + 1 =>
      let rad := kk[j]! + 1
      let e := r % rad
      go (j + 1) (r / rad) (ds.foldl (fun acc d => powsBelow N1 Sq[j]! acc d e) ds) f

/-- `Σ_{d ∈ ds} cd[d]`. -/
def sumCd (cd ds : Array Nat) : Nat := ds.foldl (fun acc d => acc + cd[d]!) 0

/-- The profile `a_q = #{d ∈ ds : d·q < N1}` for each `q ∈ Bq`. -/
def profileOf (Bq ds : Array Nat) (N1 : Nat) : Array Nat :=
  Bq.map fun q => ds.foldl (fun c d => if d * q < N1 then c + 1 else c) 0

/-- For every small pattern `pat < npat`: `patF[pat] = Σ_{d ∈ smallDivs} cd[d]`,
`profs[patProf[pat]] = profileOf Bq (smallDivs …)` (profiles deduplicated with `findIdx?`). -/
def patternData (Sq kk Bq cd : Array Nat) (N1 npat : Nat) :
    Array Nat × Array Nat × Array (Array Nat) :=
  go 0 npat (Array.emptyWithCapacity npat) (Array.emptyWithCapacity npat) #[]
where
  go (pat : Nat) : Nat → Array Nat → Array Nat → Array (Array Nat) →
      Array Nat × Array Nat × Array (Array Nat)
    | 0, patF, patProf, profs => (patF, patProf, profs)
    | f + 1, patF, patProf, profs =>
      let ds := smallDivs Sq kk N1 pat
      let v := profileOf Bq ds N1
      let patF := patF.push (sumCd cd ds)
      match profs.findIdx? (· == v) with
      | some i => go (pat + 1) f patF (patProf.push i) profs
      | none => go (pat + 1) f patF (patProf.push profs.size) (profs.push v)

/-! ## The law of `T_H` (incremental) -/

/-- The law of `T_H = ∏_{q ∈ H} (v_q + 1)` on `[0, KH]`, `H = primes[lo:hi]`:
`D[T] ≥ 2^62·P(T_H = T)` for `1 ≤ T ≤ KH` (full steps: no exponent cut, so this is the exact law
below `KH`), `E ≥ 2^62·E[T_H]`. Empty `H` iff `lo = hi` (then `D = [0, 2^62, 0, …]`). -/
structure HState where
  D : Array Nat
  E : Nat
  lo : Nat
  hi : Nat
  deriving Inhabited

/-- Empty `H`. -/
def HState.init (KH : Nat) : HState := ⟨(zeros (KH + 1)).set! 1 ONE2, ONE2, 0, 0⟩

/-- Adds the primes with index in `[i, i + fuel)` to the `T_H` law. -/
def HState.addRange (primes dns : Array Nat) (KH : Nat) (D : Array Nat) (E : Nat) (i : Nat) :
    Nat → Array Nat × Nat
  | 0 => (D, E)
  | f + 1 =>
    let q := primes[i]!
    let dn := dns[i]!
    HState.addRange primes dns KH (lawStepFull D KH (pmArr q dn (KH - 1))) (mulUp E (facE1u q dn))
      (i + 1) f

/-- Makes `H = primes[iN1:k]` (requires `iN1 ≤ lo` when `H` is nonempty: `H` only grows; else
`ok = false`). -/
def HState.extend (H : HState) (primes dns : Array Nat) (KH iN1 k : Nat) : HState × Bool :=
  if iN1 ≥ k then (H, H.lo == H.hi)
  else
    let (lo, hi) := if H.lo == H.hi then (iN1, iN1) else (H.lo, H.hi)
    let ok := iN1 ≤ lo && hi ≤ k
    let (D, E) := HState.addRange primes dns KH H.D H.E iN1 (lo - iN1)
    let (D, E) := HState.addRange primes dns KH D E hi (k - hi)
    (⟨D, E, iN1, k⟩, ok)

/-! ## Lower-tail tables of `(T, b)` per profile -/

/-- One `B`-prime step on the rows (increment `s = a_q` of `b` when `v_q ≥ 1`):
`new[b][T] = mulUp rows[b][T] pm[0] + Σ_{t(a+1) = T, 1 ≤ a < K} mulUp rows[b − s][t] pm[a]`. -/
def rowsStep (rows : Array (Array Nat)) (K s : Nat) (pm : Array Nat) : Array (Array Nat) :=
  go 0 rows.size (Array.emptyWithCapacity rows.size)
where
  go (b : Nat) : Nat → Array (Array Nat) → Array (Array Nat)
    | 0, acc => acc
    | f + 1, acc =>
      let base := dpRange (zeros (K + 1)) rows[b]! K pm 0 1
      go (b + 1) f (acc.push (if s ≤ b then dpRange base rows[b - s]! K pm 1 K else base))

/-- The lower-tail table of one profile: rows `b = 0 … bm`, columns `0 … K`. -/
structure ProfTab where
  bm : Nat
  K : Nat
  /-- lower W-value of `E[b] = Σ_i a_i ν_i/q_i` -/
  EbW : Nat
  /-- `S0[b][k] = Σ_{j ≤ k} D_b[j]` (P-values); `S1W[b][k] = ⌊(Σ_{j ≤ k} j·D_b[j]) / 2^14⌋`
  (lower W-values) -/
  S0 : Array (Array Nat)
  S1W : Array (Array Nat)
  deriving Inhabited

/-- Folds `rowsStep` over the `B` primes `i ∈ [i, i + fuel)`. -/
def rowsAll (a : Array Nat) (pmB : Array (Array Nat)) (K : Nat) (rows : Array (Array Nat))
    (i : Nat) : Nat → Array (Array Nat)
  | 0 => rows
  | f + 1 => rowsAll a pmB K (rowsStep rows K a[i]! pmB[i]!) (i + 1) f

/-- `Σ_i a[i]·⌊ν_i/q_i⌋` (lower W-value of `E[b]`). -/
def ebLoW (a Bq Bdn : Array Nat) : Nat := go 0 a.size 0
where
  go (i : Nat) : Nat → Nat → Nat
    | 0, acc => acc
    | f + 1, acc => go (i + 1) f (acc + a[i]! * (DDEN * W48 / (nuDen Bdn[i]! * Bq[i]!)))

/-- The table of the profile `a` (see the module docstring); `row0` is the law of `T_H` on
`[0, KH]` (size `KH + 1`), `pmB[i] = pmArr Bq[i] Bdn[i] (KH − 1)`, `tp1int = ⌊t(p−1)⌋`. -/
def buildTab (a Bq Bdn : Array Nat) (pmB : Array (Array Nat)) (row0 : Array Nat)
    (KH tp1int : Nat) : ProfTab :=
  let bm := a.foldl (· + ·) 0
  let K := min KH (tp1int + 2 + bm)
  let rows0 := (Array.replicate (bm + 1) (zeros (K + 1))).set! 0 (row0.extract 0 (K + 1))
  let rows := rowsAll a pmB K rows0 0 a.size
  let tabs := rows.map prefixTables
  { bm, K, EbW := ebLoW a Bq Bdn, S0 := tabs.map (·.1), S1W := tabs.map (·.2.map (· >>> 14)) }

/-! ## Leaves and the DFS -/

/-- `Σ_b (mulUp c_b S0[b][k_b] − S1W[b][k_b])` over the rows `b` with `c_b ≥ 1`, where
`c_b = ⌈(β0 + b·ω)/τ⌉` (W-value) and `k_b = ⌊c_b⌋`; `ok = false` if some `k_b > K`. -/
def corrSum (tab : ProfTab) (β0 om τ : Nat) (b : Nat) : Nat → Nat → Bool → Nat × Bool
  | 0, acc, ok => (acc, ok)
  | f + 1, acc, ok =>
    let cW := cdiv (β0 + b * om) τ
    if cW < W48 then corrSum tab β0 om τ (b + 1) f acc ok
    else
      let k := cW >>> 48
      if tab.K < k then corrSum tab β0 om τ (b + 1) f acc false
      else corrSum tab β0 om τ (b + 1) f (acc + (mulUp cW tab.S0[b]![k]! - tab.S1W[b]![k]!)) ok

/-- Upper W-value of `E_{B,H}[(τ T − β(b))⁺]` for a leaf with `τ = τ(s_S)` and `F` (lower W-value),
`β(b) = tp1 + F + b·om` (`tp1`, `om` lower W-values of `t(p−1)`, `ω = 1 − 1/p`; `omP = om·2^14`
is the **same** lower bound `ω' = om/2^48` as a P-value: the lower-tail identity must use one `ω'` in
both places), `ETW` an upper W-value of `E[T]`:
`τ·ETW + τ·corr − (tp1 + F) − ⌊omP·EbW/2^62⌋`. -/
def leafValue (tab : ProfTab) (F τ ETW tp1 om omP : Nat) : Nat × Bool :=
  let β0 := tp1 + F
  let (corr, ok) := corrSum tab β0 om τ 0 (tab.bm + 1) 0 true
  (τ * ETW + τ * corr - (β0 + mulDn omP tab.EbW), ok)

/-- Everything the DFS needs at one prime `p`. Per `S` prime `j`: `pm[j][a]` (P-values,
`a ≤ acut[j]`), `h[j][a]` (P-values, `a ≤ acut[j] + 1`), `kk[j]`, `stride[j]`;
`REW[j]` = upper W-value of `∏_{i ≥ j} E[v_i + 1]·E[T]`. -/
structure DfsCfg where
  nS : Nat
  pm : Array (Array Nat)
  acut : Array Nat
  h : Array (Array Nat)
  REW : Array Nat
  kk : Array Nat
  stride : Array Nat
  ETW : Nat
  epsAbs : Nat
  patF : Array Nat
  patProf : Array Nat
  tabs : Array ProfTab
  tp1 : Nat
  om : Nat
  omP : Nat

/-- Accumulators of the DFS (W-values). -/
structure DfsAcc where
  leaf : Nat
  prune : Nat
  nleaf : Nat
  ok : Bool

/-- A leaf: adds `mulUp P (leafValue …)`. -/
def leafAdd (c : DfsCfg) (P τ pat : Nat) (acc : DfsAcc) : DfsAcc :=
  let (v, ok) := leafValue c.tabs[c.patProf[pat]!]! c.patF[pat]! τ c.ETW c.tp1 c.om c.omP
  { acc with leaf := acc.leaf + mulUp P v, nleaf := acc.nleaf + 1, ok := acc.ok && ok }

mutual
/-- **Node** at depth `j` (exponents of `S[0:j]` fixed; `P` = upper P-value of their probability,
`τ = ∏_{i<j}(v_i+1)`, `pat` = their small-pattern index). -/
def dfsNode (c : DfsCfg) : Nat → Nat → Nat → Nat → Nat → DfsAcc → DfsAcc
  | 0, _, _, _, _, acc => { acc with ok := false }
  | f + 1, j, P, τ, pat, acc =>
    if j < c.nS then dfsExp c f j 0 P τ pat acc else leafAdd c P τ pat acc

/-- **Exponent `a` of `S[j]`**: either prune `{v_j ≥ a}` (adding its bound, a W-value) or recurse
into `v_j = a` and continue with `a + 1`. -/
def dfsExp (c : DfsCfg) : Nat → Nat → Nat → Nat → Nat → Nat → DfsAcc → DfsAcc
  | 0, _, _, _, _, _, acc => { acc with ok := false }
  | f + 1, j, a, P, τ, pat, acc =>
    let bnd := τ * mulUp (mulUp P c.h[j]![a]!) c.REW[j + 1]!
    if c.acut[j]! < a || bnd < c.epsAbs then { acc with prune := acc.prune + bnd }
    else
      let acc := dfsNode c f (j + 1) (mulUp P c.pm[j]![a]!) (τ * (a + 1))
        (pat + min a c.kk[j]! * c.stride[j]!) acc
      dfsExp c f j (a + 1) P τ pat acc
end

/-! ## The S/B/H cost -/

/-- Number of entries of the increasing array `ps` that are `< v`. -/
def countLt (ps : Array Nat) (v : Nat) : Nat := go 0 ps.size
where
  go (i : Nat) : Nat → Nat
    | 0 => i
    | f + 1 => if ps[i]! < v then go (i + 1) f else i

/-- `⌈√n⌉`. -/
def isqrtCeil (n : Nat) : Nat := let s := Nat.sqrt n; if s * s < n then s + 1 else s

/-- The split point: `y = N1` if `N1 ≤ YB`, else `max ⌈√N1⌉ N2`. -/
def splitY (YB N1 N2 : Nat) : Nat := if N1 ≤ YB then N1 else max (isqrtCeil N1) N2

/-- `∏_{i ∈ [i0, i0 + n)} f(i)` rounded up (`mulUp`), starting from `acc`. -/
def prodUp (f : Nat → Nat) (acc i : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => prodUp f (mulUp acc (f i)) (i + 1) n

/-- Mixed-radix strides `stride[j] = ∏_{i<j} (kk[i] + 1)` and the total `npat`. -/
def strides (kk : Array Nat) : Array Nat × Nat :=
  kk.foldl (fun (acc : Array Nat × Nat) k => (acc.1.push acc.2, acc.2 * (k + 1))) (#[], 1)

/-- Output of the S/B/H bound at one prime. -/
structure SbhOut where
  cost : Nat
  ok : Bool
  nleaf : Nat
  npat : Nat
  nprof : Nat

/-- **The S/B/H cost** at the prime `p = primes[k]` with δ-value `dn` (`t = dn/10^9`) and
`N1 = ⌈m/p⌉ ≥ 3`: an upper P-value of `E[(U_p(s) − t)⁺]/(1 − t)` (s over the primes below `p`,
tilts `10^9/(10^9 − dns[i])`), given `H` = the law of `T_H` for `H = primes[iN1:k]`,
`iN1 = #{primes < N1}` (see `HState.extend`). -/
def sbhCost (P : Params2) (p dn : Nat) (primes dns : Array Nat) (k : Nat) (H : HState) : SbhOut :=
  let N1 := cdiv P.m p
  let N2 := cdiv P.m (p * p)
  let y := splitY P.YB N1 N2
  let okY := decide (N1 ≤ y * y) && decide (N2 ≤ y) && decide (2 ≤ N1)
  let iS := min (countLt primes y) k           -- S = primes[0:iS]
  let iB := min (countLt primes N1) k          -- B = primes[iS:iB] (if iS ≤ iB), H = primes[iB:k]
  let iB := max iS iB
  let okH := H.lo == H.hi || (H.lo == iB && H.hi == k)
  let okH := okH && (H.lo != H.hi || iB == k)
  let Sq := primes.extract 0 iS
  let Sdn := dns.extract 0 iS
  let Bq := primes.extract iS iB
  let Bdn := dns.extract iS iB
  -- c(d), small patterns, profiles
  let cd := cdTable P.m p N1
  let kk := Sq.map (kkOf · N1)
  let (stride, npat) := strides kk
  let (patF, patProf, profs) := patternData Sq kk Bq cd N1 npat
  -- E[T] (P-value) and the lower-tail tables
  let ET := prodUp (fun i => facE1u Bq[i]! Bdn[i]!) H.E 0 Bq.size
  let pmB := (Array.range Bq.size).map fun i => pmArr Bq[i]! Bdn[i]! (P.KH - 1)
  let tp1int := dn * (p - 1) / DDEN
  let tabs := profs.map fun a => buildTab a Bq Bdn pmB H.D P.KH tp1int
  -- the DFS over S
  let acut := Sq.map acut60
  let pmS := (Array.range Sq.size).map fun j => pmArr Sq[j]! Sdn[j]! acut[j]!
  let hS := (Array.range Sq.size).map fun j => hArr Sq[j]! Sdn[j]! (acut[j]! + 1)
  let Rrest := (Array.range (Sq.size + 1)).map fun j =>
    prodUp (fun i => facE1u Sq[i]! Sdn[i]!) ONE2 j (Sq.size - j)
  let REW := Rrest.map fun r => cdiv (r * ET) (ONE2 <<< 14)
  let cfg : DfsCfg :=
    { nS := Sq.size, pm := pmS, acut, h := hS, REW, kk, stride, ETW := cdiv ET 16384,
      epsAbs := REW[0]! >>> P.epsShift, patF, patProf, tabs,
      tp1 := dn * (p - 1) * W48 / DDEN, om := W48 - cdiv W48 p, omP := (W48 - cdiv W48 p) <<< 14 }
  let acc := dfsNode cfg 100000 0 ONE2 1 0 ⟨0, 0, 0, true⟩
  { cost := cdiv (((acc.leaf + acc.prune) <<< 14) * DDEN) ((p - 1) * (DDEN - dn))
    ok := okY && okH && acc.ok && decide (dn < DDEN) && decide (2 ≤ p)
    nleaf := acc.nleaf, npat, nprof := profs.size }

end MinModulus.Checker2Impl
