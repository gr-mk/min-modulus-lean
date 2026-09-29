import MinModulus.CheckerImpl.Moments
/-
# `MinModulus.CheckerImpl.Enum` — exact enumeration of the small part `s_A ≤ X_p`

Status: complete, no `sorry`. Core Lean only.

Fix a prime `p` in the comparison range, the thresholds `M_j = ⌈m/p^j⌉` and `J` = least `j ≥ 1`
with `M_J = 1` (`J ≤ 3` is required). The A-primes `A = (q_0 < q_1 < … )` are the primes `≤ z`.
For `s = Π q_i^{v_i}` (a *leaf*):
* `P(s_A = s) = C[pat] / s` **exactly**, where `pat` records which *tilted* A-primes (δ > 0)
  have `v ≥ 1`, and `C[pat] = Π_{untilted q} (q−1)/q · Π_{tilted q ∉ pat} (1 − ν_q/q) ·
  Π_{tilted q ∈ pat} ν_q (q−1)/q` (because `P(v_q = a) = (factor) · q^{−a}` in each case);
  `cup[pat] ≥ 2^62·C[pat] ≥ clo[pat]`.
* `σ_1 = #{d | s : d < M_1}` and `σ_2 = #{d | s : d < M_2}` (small divisors; `M_2 = 1` if `J ≤ 2`,
  `M_1 = 1` if `J = 1`), `n_1 = τ(s) − σ_1`, and
  `U_A(s) = Σ_{d | s} w_p(d) = I / (p^{J−1} (p−1))` with
  `I = p^{J−1} n_1 + p^{J−2} (σ_1 − σ_2) + σ_2` (a natural number; `pj1 = p^{J−1}`,
  `pj2 = p^{J−2}`, `pj2 = 0` when `J = 1`). (`w_p(d) = p^{1−j0(d)}/(p−1)`, `j0(d) = 1` iff
  `d ≥ M_1`, `= 2` iff `M_2 ≤ d < M_1`, `= 3` iff `d < M_2`.)

The recursion visits **every exponent vector with `s ≤ X` exactly once** (primes in increasing
order; `s · q_i > X` ⇒ all remaining exponents are 0). The small divisors of the current `s` are
kept, without repetition, in `buf[0:len]` (stack discipline); raising the exponent of `q` from
`a−1` to `a` appends `{e·q : e in the previous block, e·q < M_1}` (the small divisors with
`q`-exponent exactly `a`).

Accumulators (all entries are sums of P-values):
* `pen[k] = Σ_{leaves s, τ(s) = k ≤ KMAX} ⌊clo[pat]/s⌋` (lower bound of the enumerated mass);
* "linear" leaves (`I ≥ It`, i.e. `U_A(s) ≥ t`): `hn[n_1]`, `hs1[σ_1]`, `hs2[σ_2]` each receive
  `⌈cup[pat]/s⌉`;
* "FB" leaves (`I < It`): `fb[(n_1·M_1 + σ_1)·M_2 + σ_2]` receives `⌈cup[pat]/s⌉`.
-/
namespace MinModulus.CheckerImpl

/-- Per-prime configuration of the enumeration. -/
structure EnumCfg where
  /-- A-primes, increasing. -/
  aps : Array Nat
  /-- pattern bit of each A-prime (`0` if its δ is 0). -/
  bits : Array Nat
  /-- enumerate `s ≤ X`. -/
  X : Nat
  M1 : Nat
  M2 : Nat
  pj1 : Nat
  pj2 : Nat
  /-- a leaf is linear iff `I ≥ It` (`It = ⌈δ_p · p^{J−1}(p−1)⌉`). -/
  It : Nat
  /-- `n_1 < n1max` for every FB leaf. -/
  n1max : Nat
  cup : Array Nat
  clo : Array Nat
  kmax : Nat

/-- Accumulators of the enumeration (see the module docstring). -/
structure EnumAcc where
  buf : Array Nat
  pen : Array Nat
  hn : Array Nat
  hs1 : Array Nat
  hs2 : Array Nat
  fb : Array Nat
  nleaf : Nat
  ok : Bool

/-- Processes one leaf `s` with `τ = τ(s)`, pattern `pat`, `σ1 = σ_1(s)`, `σ2 = σ_2(s)`.
(The accumulator is destructured first so that every array is updated in place.) -/
def leaf (cfg : EnumCfg) (s τ pat σ1 σ2 : Nat) (acc : EnumAcc) : EnumAcc :=
  match acc with
  | ⟨buf, pen, hn, hs1, hs2, fb, nleaf, ok⟩ =>
    let pu := cdiv (getD0 cfg.cup pat) s
    let pl := getD0 cfg.clo pat / s
    let pen := if τ ≤ cfg.kmax then growAdd pen τ pl else pen
    let n1 := τ - σ1
    let I := cfg.pj1 * n1 + cfg.pj2 * (σ1 - σ2) + σ2
    let ok := ok && σ1 ≤ τ && σ2 ≤ σ1 && σ1 < cfg.M1 + 1
    if cfg.It ≤ I then
      ⟨buf, pen, growAdd hn n1 pu, growAdd hs1 σ1 pu, growAdd hs2 σ2 pu, fb, nleaf + 1, ok⟩
    else
      ⟨buf, pen, hn, hs1, hs2, growAdd fb ((n1 * cfg.M1 + σ1) * cfg.M2 + σ2) pu, nleaf + 1,
        ok && n1 < cfg.n1max && σ1 < cfg.M1 && σ2 < cfg.M2⟩

/-- Appends `e·q` for every `e = buf[i]`, `i ∈ [i0, be)`, with `e·q < M1`, at positions
`len, len+1, …`; returns the accumulator, the new length, and the new count of entries `< M2`. -/
def extendBlock (cfg : EnumCfg) (q be : Nat) : Nat → Nat → Nat → EnumAcc → Nat → EnumAcc × Nat × Nat
  | i, len, sig2, acc, 0 => if i < be then ({ acc with ok := false }, len, sig2) else (acc, len, sig2)
  | i, len, sig2, acc, f + 1 =>
    if i < be then
      let v := getD0 acc.buf i * q
      if v < cfg.M1 then
        if len < acc.buf.size then
          let acc := match acc with
            | ⟨buf, pen, hn, hs1, hs2, fb, nleaf, ok⟩ => ⟨buf.set! len v, pen, hn, hs1, hs2, fb, nleaf, ok⟩
          extendBlock cfg q be (i + 1) (len + 1) (if v < cfg.M2 then sig2 + 1 else sig2) acc f
        else ({ acc with ok := false }, len, sig2)
      else extendBlock cfg q be (i + 1) len sig2 acc f
    else (acc, len, sig2)

mutual
/-- **Node** at level `i` with current value `s` (exponents of `q_0 … q_{i−1}` fixed):
visits all leaves `s · Π_{j ≥ i} q_j^{v_j} ≤ X`, each once.
Precondition: `buf[0:len]` = the divisors of `s` below `M1` (no repetition), `sig2` = how many
of them are `< M2`, `τ = τ(s)`, `pat` = pattern of `s`. `fuel` bounds the recursion depth
(running out sets `ok := false`). -/
def enumNode (cfg : EnumCfg) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → EnumAcc → EnumAcc
  | 0, _, _, _, _, _, _, acc => { acc with ok := false }
  | f + 1, i, s, τ, pat, len, sig2, acc =>
    if i < cfg.aps.size && s * getD0 cfg.aps i ≤ cfg.X then
      let q := getD0 cfg.aps i
      -- exponent 0 of q
      let acc := enumNode cfg f (i + 1) s τ pat len sig2 acc
      -- exponents a ≥ 1 of q (the first new block is built from buf[0:len])
      enumExp cfg f i q (s * q) 1 τ (pat ||| getD0 cfg.bits i) 0 len len sig2 acc
    else leaf cfg s τ pat len sig2 acc

/-- **Exponent `a ≥ 1` of `q = q_i`**: current value `sa = s · q^a ≤ X` where `s` is the node
value; `τ0 = τ(s)`; `buf[bs:be]` = small divisors of `s·q^(a−1)` with `q`-exponent exactly
`a − 1`; `buf[0:len]` = all small divisors of `s·q^(a−1)` (`be = len`). -/
def enumExp (cfg : EnumCfg) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → EnumAcc → EnumAcc
  | 0, _, _, _, _, _, _, _, _, _, _, acc => { acc with ok := false }
  | f + 1, i, q, sa, a, τ0, pat, bs, be, len, sig2, acc =>
    let (acc, len', sig2') := extendBlock cfg q be bs len sig2 acc (be - bs + 1)
    let acc := enumNode cfg f (i + 1) sa (τ0 * (a + 1)) pat len' sig2' acc
    if sa * q ≤ cfg.X then enumExp cfg f i q (sa * q) (a + 1) τ0 pat len len' len' sig2' acc
    else acc
end

/-- Runs the enumeration for a configuration: starts at `s = 1` (small divisors `{1}` if
`1 < M1`). -/
def runEnum (cfg : EnumCfg) (bufSize : Nat) : EnumAcc :=
  let len := if 1 < cfg.M1 then 1 else 0
  let sig2 := if 1 < cfg.M2 then 1 else 0
  let buf := (Array.replicate (bufSize + 2) 0).set! 0 1
  enumNode cfg 100000 0 1 1 0 len sig2 ⟨buf, #[], #[], #[], #[], #[], 0, true⟩

end MinModulus.CheckerImpl
