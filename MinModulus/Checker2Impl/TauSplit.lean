import MinModulus.Checker2Impl.Laws
/-
# `MinModulus.Checker2Impl.TauSplit` — the τ-split bound (`N1 = ⌈m/p⌉ ≤ 2`) and its blocks

Status: complete, no `sorry`. Core Lean only.

## The mathematics (math layer: `Checker2Math/Identities.lean`)
For `N1 ≤ 2` the only divisor `d < N1` of `s` is `d = 1` (when `p < m`), so exactly
`(p − 1)·U_p(s) = τ(s) − c1`, `c1 = [p < m]·c(1)` (`Up_identity`; `c(1) = 1 − 1/p` since
`p < m ≤ 2p ≤ p²`). Split the primes below `p` into `s` = the primes `< YS` (YS = the first prime with
`N1 ≤ 2`) and `l` = the primes in `[YS, p)` (for blocks: every number of `[YS, p')` that the sieve
leaves unmarked, a superset of the primes). Then `τ = τ_s·τ_l`, `τ_l = ∏_l (v_q + 1) ≤ 2^e` with
`e = Σ_l v_q` (`a + 1 ≤ 2^a`), so for `X = c1 + t(p−1)`, by independence,
```
E[(τ − X)⁺] ≤ E[(τ_s·2^e − X)⁺] = Σ_e 2^e P(e)·E[(τ_s − X/2^e)⁺]
            ≤ Σ_{e ≤ NN} W_e[e]·Gs(X/2^e) + E[τ_s]·E[2^e; lost_e].
```
**Weighted laws.** Both DPs store *weighted* masses (upper P-values): `W[T] ≥ T·P(τ_s = T, kept)`
and `W_e[e] ≥ 2^e·P(e, kept)`. With round-up fixed point a negligible mass sits at `≥ 1` ulp; stored
unweighted it would be amplified by the weights `T ≤ TS` resp. `2^e ≤ 2^NN` of the final sums
(this was measured: up to `7.6·10^-3` relative at `p = 2·10^5`); stored weighted it never is.
* `τ_s` (`TauSState`): the TauLaw DP on `[0, TS]` with exponent cut `acut60 q`, multipliers
  `(a+1)·P(v = a)` (`weightByTau`), the lost mass `lost ≥ E[τ_s; ¬kept]` by the recursion
  `lost ← lost·E[v+1] + Σ_t W[t]·h(min(⌊TS/t⌋, ac+1))` (`TauLaw.lostMass_insert_le`,
  `P(t)·t = W[t]`), and `E ≥ E[τ_s]`.
* `Gs(y)` (`gsUp`), an upper bound of `E[(τ_s − y)⁺]` for `y ≥ 0`: `E[τ_s] − y` if `y < 1`
  (`τ_s ≥ 1`); `lost` if `⌊y⌋ + 1 > TS`; else, with `k = ⌊y⌋ + 1`,
  `SW[k] − y·SV[k]/2^20 + lost ≥ Σ_{T ≥ k} (1 − y/T)·W[T] + lost ≥ Σ_{T > y} (T − y) P(T) + lost`.
  `y` is a *lower* bound of the threshold.
* the e-law (`ELaw`): `W[e] ≥ 2^e·P(Σ_l v_q = e, kept)` for `e ≤ NN`, `lost ≥ E[2^e; ¬kept]` (a path
  is lost when the running sum exceeds `NN` or an exponent exceeds `acut60 q`); multipliers
  `2^a·P(v = a)` (`weightByPow2`); recursion
  `lost ← lost·E[2^v] + Σ_e (Σ_{a ≤ ac, e+a > NN} W[e]·2^a P(v=a) + W[e]·E[2^v 1{v > ac}])`.
The cost is `cdiv (val·10^9) ((p−1)(10^9 − dn))` (the division by `(p−1)(1−t)`).
For a block `[B, B')` (constant δ): the e-law contains every unmarked number `< B'`, the threshold
is taken at `B` and the division by `(B−1)(1−t)`; both are monotone in `p`, so the value bounds the
cost of every prime of the block.
-/
namespace MinModulus.Checker2Impl

open MinModulus.CheckerImpl

/-! ## The weighted law of `τ_s` (primes `< YS`) -/

/-- State of the `τ_s` DP on `[0, TS]` (see the module docstring): `W[T] ≥ T·P(τ_s = T, kept)`,
`lost ≥ E[τ_s; ¬kept]`, `E ≥ E[τ_s]` (P-values). -/
structure TauSState where
  W : Array Nat
  lost : Nat
  E : Nat
  deriving Inhabited

/-- `τ_s = 1`. -/
def TauSState.init (TS : Nat) : TauSState := ⟨(zeros (TS + 1)).set! 1 ONE2, 0, ONE2⟩

/-- Adds the prime `q` (δ-value `dn`) with exponent cut `ac = acut60 q`. -/
def TauSState.add (st : TauSState) (TS q dn : Nat) : TauSState :=
  let ac := acut60 q
  let pm := pmArr q dn ac
  let hA := hArr q dn (ac + 1)
  { W := dpRange (zeros (TS + 1)) st.W TS (weightByTau pm) 0 (ac + 1)
    lost := mulUp st.lost (facE1u q dn) + lostSumW st.W TS ac hA
    E := mulUp st.E (facE1u q dn) }

/-- The frozen suffix tables of `τ_s` (`suffixTablesW`). -/
structure TauSTab where
  SW : Array Nat
  SV : Array Nat
  TS : Nat
  E : Nat
  lost : Nat
  deriving Inhabited

/-- Freezes the `τ_s` law into suffix tables. -/
def TauSState.freeze (st : TauSState) (TS : Nat) : TauSTab :=
  let (SW, SV) := suffixTablesW st.W TS
  ⟨SW, SV, TS, st.E, st.lost⟩

/-- Upper P-value of `Gs(y) = E[(τ_s − y)⁺]` for `y = yP/2^62 ≥ 0` (see the module docstring). -/
def gsUp (tb : TauSTab) (yP : Nat) : Nat :=
  if yP < ONE2 then tb.E - yP
  else
    let k := yP / ONE2 + 1
    if tb.TS < k then tb.lost
    else (tb.SW[k]! - ((yP * tb.SV[k]!) >>> 82)) + tb.lost

/-! ## The weighted e-law (primes / unmarked numbers in `[YS, p)`) -/

/-- `W[e] ≥ 2^62·2^e·P(e, kept)` for `e ≤ NN` (size `NN + 1`); `lost ≥ 2^62·E[2^e; ¬kept]`. -/
structure ELaw where
  W : Array Nat
  lost : Nat
  deriving Inhabited

/-- `e = 0`. -/
def ELaw.init (NN : Nat) : ELaw := ⟨(zeros (NN + 1)).set! 0 ONE2, 0⟩

/-- Inner loop over the exponents `a ∈ [a, a + fuel)` from the state `e` with weighted mass `w`
(multipliers `mu[a] ≥ 2^a·P(v = a)`): kept targets `e + a ≤ NN` are added to `Wn`, the others to the
lost sum. -/
def eInner (NN : Nat) (mu : Array Nat) (w e : Nat) (a : Nat) :
    Nat → Array Nat × Nat → Array Nat × Nat
  | 0, acc => acc
  | f + 1, (Wn, Ls) =>
    let v := mulUp w mu[a]!
    if e + a ≤ NN then eInner NN mu w e (a + 1) f (Wn.set! (e + a) (Wn[e + a]! + v), Ls)
    else eInner NN mu w e (a + 1) f (Wn, Ls + v)

/-- Outer loop over the states `e ∈ [e, e + fuel)`. -/
def eOuter (NN : Nat) (W mu : Array Nat) (ac h2 : Nat) (e : Nat) :
    Nat → Array Nat × Nat → Array Nat × Nat
  | 0, acc => acc
  | f + 1, acc =>
    let w := W[e]!
    if w == 0 then eOuter NN W mu ac h2 (e + 1) f acc
    else
      let (Wn, Ls) := eInner NN mu w e 0 (ac + 1) acc
      eOuter NN W mu ac h2 (e + 1) f (Wn, Ls + mulUp w h2)

/-- Adds the number `q ≥ 3` (δ-value `dn`) to the e-law, exponent cut `ac = acut60 q`. -/
def ELaw.add (st : ELaw) (NN q dn : Nat) : ELaw :=
  let ac := acut60 q
  let mu := weightByPow2 (pmArr q dn ac)
  let (Wn, Ls) := eOuter NN st.W mu ac (h2Up q dn (ac + 1)) 0 (NN + 1) (zeros (NN + 1), 0)
  ⟨Wn, mulUp st.lost (e2Up q dn) + Ls⟩

/-! ## The τ-split value -/

/-- `Σ_{e ≤ NN} mulUp W[e] (Gs(⌊X/2^e⌋)) + mulUp E[τ_s] lost_e`, an upper P-value of
`E[(τ_s·2^e − X)⁺]` for `X = XP/2^62` (`XP` a lower P-value of the threshold). -/
def splitVal (tb : TauSTab) (el : ELaw) (NN XP : Nat) : Nat := go 0 (NN + 1) (mulUp tb.E el.lost)
where
  go (e : Nat) : Nat → Nat → Nat
    | 0, acc => acc
    | f + 1, acc =>
      let w := el.W[e]!
      if w == 0 then go (e + 1) f acc
      else go (e + 1) f (acc + mulUp w (gsUp tb (XP >>> e)))

/-- Lower P-value of the τ-split threshold `X = c1 + t(p−1)` at `p` (δ-value `dn`, `N1 ≤ 2`):
`c1 = [p < m]·(1 − 1/p)` (`j0(1) = 2` since `p < m ≤ 2p ≤ p²`). -/
def splitThreshold (m p dn : Nat) : Nat :=
  (if p < m then ONE2 - cdiv ONE2 p else 0) + dn * (p - 1) * ONE2 / DDEN

/-- **The τ-split cost** at `p` (δ-value `dn`): upper P-value of `E[(U_p − t)⁺]/(1 − t)`. -/
def splitCost (m NN p dn : Nat) (tb : TauSTab) (el : ELaw) : Nat :=
  cdiv (splitVal tb el NN (splitThreshold m p dn) * DDEN) ((p - 1) * (DDEN - dn))

end MinModulus.Checker2Impl
