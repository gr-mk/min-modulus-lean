import MinModulus.Checker2Math.Identities
import MinModulus.Checker2Math.Laws
import MinModulus.CheckerMath.Glue
import MinModulus.Checker2Impl.Checker

/-!
# `Checker2Sound.Defs`: the shared vocabulary of the second soundness proof

STATUS: definitions only (lean2 stage 1; no proofs). Owned by the assembly agent (L2-E).
Every stage-2 agent imports **this** file (never `Interfaces.lean`, which imports theirs).

## Conventions
* `pv x = x / 2^62` (P-values), `wv x = x / 2^48` (W-values, the per-leaf scale of `SBH.lean`).
* `delta2 P = deltaPairR (deltaCert2 P)`: **the certificate's δ**, `deltaN2 P p / 10^9` for
  `p ≤ X`, `1/2` beyond. Its tilt is exact (`CheckerMath.tilt_deltaPairR`):
  `nu2 P q = 10^9/(10^9 − deltaN2 P q)` for `q ≤ X`. For a non-prime `q ≤ X` (a number the sieve
  leaves unmarked in the block phase; formally possible, never the case) `nu2 P q` is still a valid
  tilt `≤ 2 ≤ q`.
* `primes2 P = primesUpTo P.PX`, `dns2 P = (primes2 P).map (deltaN2 P)` (exactly what `run2` uses),
  `idxSet P lo hi` = the set of `primes2 P [i]`, `lo ≤ i < hi`.
* Syntax note: with Mathlib imported, `![` is a token (vector notation), so write `(a[i]!)[j]!`,
  not `a[i]![j]!` (`tabS0`, `tabS1W`).
* Caps: every DP statement is for uniform caps `N ≥ N0` (the arrays use untruncated point masses,
  equal to `Smooth.rho` below the cap): `N0 = KH` for the `T_H`/`(T, b)` tables (exponents up to
  `KH − 1`), `N0 = 64` for `τ_s` and the e-law (`acut60 ≤ 60`). Final statements are for all caps
  (`CheckerMath.hingeLoss_le_of_forall_ge`).

## State invariants (contracts between the agents)
* `HValid P H`: `H` holds the exact law of `T_H` on `[0, KH]` for `H = idxSet P H.lo H.hi`.
* `TauSValid P st S`: `st` is the **weighted** τ_s DP for the set of primes `S`.
* `ELawValid P el L`: `el` is the **weighted** e-DP for the set of numbers `L`.
-/

namespace MinModulus.Checker2Sound

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Main MinModulus.Smooth

/-- The real number represented by a P-value: `x / 2^62`. -/
noncomputable def pv (x : ℕ) : ℝ := (x : ℝ) / 2 ^ 62

/-- The real number represented by a W-value: `x / 2^48`. -/
noncomputable def wv (x : ℕ) : ℝ := (x : ℝ) / 2 ^ 48

/-- **The certificate's δ**: `deltaN2 P p / 10^9` for `p ≤ X`, `1/2` for `p > X`. -/
noncomputable def delta2 (P : Params2) : ℕ → ℝ := deltaPairR (deltaCert2 P)

/-- The tilts of the certificate: `tilt (delta2 P)`. -/
noncomputable def nu2 (P : Params2) : ℕ → ℝ := tilt (delta2 P)

/-- The primes `≤ PX` (increasing), as used by `run2`. -/
def primes2 (P : Params2) : Array ℕ := primesUpTo P.PX

/-- Their δ-values, as used by `run2`. -/
def dns2 (P : Params2) : Array ℕ := (primes2 P).map (deltaN2 P)

/-- The set `{primes2 P [i] : lo ≤ i < hi}`. -/
def idxSet (P : Params2) (lo hi : ℕ) : Finset ℕ :=
  (((primes2 P).toList.drop lo).take (hi - lo)).toFinset

/-- The profile of an S/B/H table as a function on the primes: `a[i]` at `Bq[i]`, `0` elsewhere
(`List.idxOf` is `Bq.size` off `Bq`, and `a[Bq.size]! = 0` when `a.size = Bq.size`). -/
def profileFn (Bq a : Array ℕ) (q : ℕ) : ℕ := a[Bq.toList.idxOf q]!

/-- Entry `(b, k)` of the prefix table `S0` of an S/B/H profile table. -/
def tabS0 (tab : ProfTab) (b k : ℕ) : ℕ := (tab.S0[b]!)[k]!

/-- Entry `(b, k)` of the prefix table `S1W` of an S/B/H profile table. -/
def tabS1W (tab : ProfTab) (b k : ℕ) : ℕ := (tab.S1W[b]!)[k]!

/-- **`HValid P H`**: the `T_H` state holds (upper bounds of) the exact law of
`T_H = ∏_{q ∈ H} (v_q + 1)` on `[0, KH]` and of `E[T_H]`, for `H = idxSet P H.lo H.hi`. -/
structure HValid (P : Params2) (H : HState) : Prop where
  idx : H.lo ≤ H.hi ∧ H.hi ≤ (primes2 P).size
  size : H.D.size = P.KH + 1
  law : ∀ N, P.KH ≤ N → ∀ k, k ≤ P.KH →
    lawTau (idxSet P H.lo H.hi) (nu2 P) (fun _ => N) k ≤ pv H.D[k]!
  mean : ∏ q ∈ idxSet P H.lo H.hi, (1 + nu2 P q / ((q : ℝ) - 1)) ≤ pv H.E

/-- **`TauSValid P st S`**: the weighted `τ_s` DP for the set `S` of primes (table `[0, TS]`,
exponent cut `acut60`): `W[T] ≥ T·P(τ_S = T, kept)`, `lost ≥ E[τ_S; ¬kept]`,
`E ≥ ∏_{q ∈ S} (1 + ν_q/(q−1)) ≥ E[τ_S]`. -/
structure TauSValid (P : Params2) (st : TauSState) (S : Finset ℕ) : Prop where
  mem : ∀ q ∈ S, q.Prime ∧ q ≤ P.X
  size : st.W.size = P.TS + 1
  law : ∀ N, 64 ≤ N → ∀ T, T ≤ P.TS →
    (T : ℝ) * lawKept S (nu2 P) (fun _ => N) P.TS acut60 T ≤ pv st.W[T]!
  lost : ∀ N, 64 ≤ N → lostMass S (nu2 P) (fun _ => N) P.TS acut60 ≤ pv st.lost
  mean : ∏ q ∈ S, (1 + nu2 P q / ((q : ℝ) - 1)) ≤ pv st.E

/-- **`ELawValid P el L`**: the weighted e-DP for the set `L` of numbers `≥ 3` (table `[0, NN]`,
exponent cut `acut60`): `W[e] ≥ 2^e·P(e, kept)`, `lost ≥ E[2^e; ¬kept]`. -/
structure ELawValid (P : Params2) (el : ELaw) (L : Finset ℕ) : Prop where
  mem : ∀ q ∈ L, 3 ≤ q ∧ q ≤ P.X
  size : el.W.size = P.NN + 1
  law : ∀ N, 64 ≤ N → ∀ e, e ≤ P.NN →
    (2 : ℝ) ^ e * lawE L (nu2 P) (fun _ => N) P.NN acut60 e ≤ pv el.W[e]!
  lost : ∀ N, 64 ≤ N → lostE L (nu2 P) (fun _ => N) P.NN acut60 ≤ pv el.lost

end MinModulus.Checker2Sound
