import MinModulus.CheckerMath.Split
import MinModulus.CheckerMath.UpCount
import MinModulus.Main.Certificate

/-!
# `CheckerMath.ComparisonBound`: the comparison bound (`31 ≤ p ≤ 2·10^5`) in exact reals

STATUS: complete. No `sorry`, no `admit`, no new axioms (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`; see `CheckerMath/ComparisonBoundAxioms.lean`). Owned by the
CheckerMath (comparison-bound) agent: files `TauLaw`, `GFun`, `Split`, `UpCount`,
`ComparisonBound`, `ComparisonBoundAxioms` (the files `HingeTilt`, `FirstMoment`, `Moment`, `Glue` of this directory
belong to the first-moment/moments/glue agent; both sets import together without clashes).

This module is the *mathematical algorithm layer* of the comparison bound of `rigcert.c`
(and of the Lean checker `CheckerImpl`): a chain of inequalities between real numbers, stated
for abstract arrays `D : ℕ → ℝ`, so that the code-level soundness proof only has to show that
the code computes upper (resp. lower) bounds of the real expressions below.

## Files
* `TauLaw.lean` : `tauN`, `Kept`, `lawKept`, `lostMass`, `expLostProb`, `hMass`, `lostThr`; the
  DP step (`lawKept_insert`, `lawKept_insert_le`, `le_lawKept_insert`), the lost-mass recursion
  (`lostMass_insert`, `lostMass_insert_le`), one-prime bounds uniform in the cap
  (`expect1_add_one_le`, `expect1_hA_le`, `hMass_le_lostThr`), decompositions
  (`expect_kept_eq_sum`, `expect_tauN_eq`), `expect_tauN_le`, the union bound `expLostProb_le`,
  caps (`rho_eq_pointMass`, `lostMass_mono_cap`, `lostMass_le_of_forall_ge`,
  `lawKept_congr_cap`); pull form `lawKept_insert_pull`; the exact law `lawTau`
  (`lawTau_empty`, `lawTau_insert`, `lawKept_eq_lawTau`).
* `GFun.lean`   : `meanTau`, `FB`, `GB`; `GB_eq_mul_FB`, `GB_eq_of_le`, `FB_eq_of_le_one`,
  `GB_mono`, `FB_antitone`, `GB_diag_le(_of)`; `FB_le_kept` (rigcert), `FB_le_lowerTail`
  (checker); suffix sums `sufS0`/`sufSS`, `sum_hinge_eq_suffix`, `FB_le_suffix`; prefix sums
  `preS0`, `sum_lowerHinge_eq_prefix`, `FB_le_prefix`; rounded-input forms `GB_le_of_bounds`,
  `GB_le_of_ge_bounds`; `lostMass_le_of_lower` (checker's `tailA`), `meanTau_le`,
  `meanTau_mono_cap`; `FB_le_meanTau`, `FB_le_of_meanTau_le` (`fbUp`'s fallback),
  `sum_GB_linear_le` (aggregated linear leaves).
* `UpCount.lean`: leaf data of the enumeration: `weight_eq_div_smooth` (`P(s_A = s) = C[pat]/s`),
  `Up_eq_sigma` + `wp_eq_levels` (`U_A(s)` from the small-divisor counts `σ_1, σ_2`),
  `cdiv_le_iff_le_mul` (`⌈m/P⌉ ≤ d ↔ m ≤ d P`).
* `Split.lean`  : `expect_hinge_le_split` (A/B split), `restMass`, `enumMass`, `restMass_eq`,
  `expect_GB_le_enum` (enumerated vs. remainder), the DFS enumeration `enumSum`
  (`enumSum_insert`, `enumSum_empty`, `enumSum_eq_zero`, `sum_filter_smooth_le_eq_enumSum`).
* this file     : `comparison_bound` (the whole chain at fixed caps and tilts),
  `hingeLoss_le_split_tilt`, `hingeLoss_le_comparison` (for `Main.hingeLoss`),
  `hingeLoss_le_of_forall_ge`, `hingeLoss_le_of_comparison` (**all caps**, the form needed by
  `Main.Cert.loss_le`), `primesBelow_filter_union`, `primesBelow_filter_disjoint`,
  `GB_empty`, `meanTau_empty`.

## The chain (for a prime `p`, `t = δ_p ∈ [0, 1)`, any partition `primesBelow p = A ⊔ B`)
With `α_a = τ_A(a)/(p-1)`, `U_A(a) = U_p(s_A(a))`, `G = GB B ν γ t`:
```
hingeLoss m δ p γ
  ≤ E_{A∪B,ν,γ}[(U_p(s) - t)^+/(1-t)]                         (hingeLoss_le_split_tilt: ν ≥ tilt δ)
  ≤ (1/(1-t)) E_A[G(α_a, U_A(a))]                              (expect_hinge_le_split)
  ≤ (1/(1-t)) ( Σ_{a ∈ E} π(a) G(α_a, U_A(a))                   (expect_GB_le_enum)
               + Σ_{k ≤ KM} R_k G(k/(p-1), k/(p-1)) + LA·EB/(p-1) )
```
and then, for each `G(α, u)`:
* `u ≥ t`: `G(α, u) = u - t + (E[τ_B] - 1) α` (`GB_eq_of_le`, `GB_le_of_ge_bounds`);
* `α > 0`: `G(α, u) = α FB(c)`, `c = 1 + (t - u)/α` (`GB_eq_mul_FB`, `GB_le_of_bounds`);
* `FB(c) = E[(τ_B - c)^+]`:
  - `c ≤ 1`: `= E[τ_B] - c` (`FB_eq_of_le_one`);
  - rigcert: `≤ SS[k+1] + (k - c) S0[k] + L`, `k = ⌊c⌋ + 1` (`FB_le_suffix`), `L ≥ E[τ_B; lost]`;
  - checker: `≤ EB - c + Σ_{i<k} P0[i] + (c - k) P0[k] + c·P`, `k = ⌊c⌋` (`FB_le_prefix`);
* the DP arrays: `D ≥ P(τ = ·, kept)` by `lawKept_empty` + `lawKept_insert_le` (one prime at a
  time, any order), lower arrays by `le_lawKept_insert`, the lost mass by `lostMass_empty` +
  `lostMass_insert_le` + `expect1_add_one_le` + `hMass_le_lostThr` (rigcert), or by
  `lostMass_le_of_lower` (checker's `tailA`), or `expLostProb_le` (checker's B `lost`).

## Caps (uniformity over all caps `N`)
All identities hold at every cap. The DP arrays are built from the untruncated point masses
`P(V = a)`, which equal `ρ(q, ν, N, a)` for `a < N` (`rho_eq_pointMass`); so the DP bounds hold
for every uniform cap `N > max acut` (`lawKept_congr_cap`: the kept law is then cap-independent).
`hingeLoss_le_of_comparison` needs the hypotheses only for `N ≥ N0`; smaller caps follow by
monotone coupling (`Main.hingeLoss_mono_cap`, i.e. `Smooth.expect_mono_cap`). The bounds
`expect1_add_one_le`, `expect1_hA_le`, `expLostProb_le`, `expect_tauN_le` hold for every cap.

## Alignment with the landed `CheckerImpl` (`TauDP.lean`, `Enum.lean`, `Checker.lean`)
Certificate data: `δ₀ p = deltaN P p / 10^9` exactly, exact tilts `ν_q = 10^9/(10^9 - dn_q)`
(`= Main.tilt δ₀ q`); P-values are numerators over `2^62`. Per prime `p` (comparison range):
| code | real statement proved here |
|---|---|
| partition `A = primes[0:nAz]`, `B` = primes in `(z, p)` | `hAB`, `hdisj` of `hingeLoss_le_comparison` (any partition) |
| exact tilts | `hingeLoss_le_split_tilt` with `ν := Main.tilt δ₀` (`hν` from `Main.tilt_mem`) |
| `mkExpLaw` point masses `up[a] ≥ P(v = a) ≥ dn[a]` | `rho_eq_pointMass` (`ρ = P(V = a)` for `a < N`, caps `N > acut`) |
| `dpStep true` (`BState.D`, `AState.up`) | `lawKept_empty` + `lawKept_insert_le` (push form, `TM = size - 1`) |
| `dpStep false` (`AState.dn`) | `le_lawKept_insert` |
| `BState.EB`, `AState.EA` (`facE1 = 1 + ν/(q-1)`) | `meanTau_le` (every cap) |
| `BState.lost` (`Σ lostUp`, `lostUp ≥ ν q^{-(acut+1)}`) | `expLostProb_le` (union bound, every cap) |
| `AState.tailA = EA - Σ_k k·dn[k]` | `lostMass_le_of_lower` |
| `fbTable` + `fbUp`, branch `⌊c⌋ < S0.size` | `FB_le_prefix` (`2^20·PP[k0] ≥ Σ_{i<k0} P0[i]`, `fr·S0[k0] = (c-k0) P0[k0]`) |
| `fbUp`, fallback `EB` | `FB_le_of_meanTau_le` |
| `gUp` (FB case, `u < t`, `cP ≤ 2^62 c`) | `GB_le_of_bounds` with `α = α' = τ/(p-1)`, `u = u' = uNum/uDen`, `F = fb(cP)/2^62` |
| linear leaves `lin1 + lin2` (`I ≥ It` ⇒ `U_A ≥ t`) | `sum_GB_linear_le` (`w` = the leaf P-values `⌈cup/s⌉ ≥ π(a)`, `G ≥ 0`) |
| `remaining`: `R_k = up[k] - pen[k]` | `restMass_eq` (`pen[k] ≤ enumMass k`; needs `X_p ≤ 2^62 < q^{acutA+1}`) |
| `remaining`: `remlin` / `remfb` | `sum_GB_linear_le` / `GB_le_of_ge_bounds` with `u = α = k/(p-1)`; `GB_le_of_bounds` |
| `tailPart = ⌈tailA·EB/((p-1)2^62)⌉` | the `LA·EB/(p-1)` term of `comparison_bound` |
| `cost = ⌈total·10^9/(10^9 - dn)⌉` | the division by `1 - δ_p` in `comparison_bound` |
| Enum leaf probability `C[pat]/s` | `weight_eq_div_smooth` (untilted primes: both factors `(q-1)/q`) |
| Enum `n_1`, `σ_1`, `σ_2`, `I/(p^{J-1}(p-1))` | `Up_eq_sigma`, `cdiv_le_iff_le_mul` (`m ≤ p^3`, i.e. `J ≤ 3`) |
| Enum visits every `s ≤ X_p` once | `enumSum_insert`, `enumSum_eq_zero`, `sum_filter_smooth_le_eq_enumSum` |
| all caps (`Cert.loss_le`) | `hingeLoss_le_of_comparison`, `N0 = 65` suffices (all `acut ≤ 64`, `X_p ≤ 2^62`) |

Further notes:
1. `t = δ_p` exactly (the certificate's integrand is `(U - δ_p)^+/(1 - δ_p)`). An upward rounded
   tilt would also be admissible (`hingeLoss_le_split_tilt` only needs `tilt δ q ≤ ν q ≤ q`), but a
   rounded `δ'_p = 1 - 1/ν_p` may not be used as the certificate's `δ` with `t < δ'_p`:
   `(U - δ')^+/(1 - δ') ≤ (U - t)^+/(1 - t)` fails for `U > 1`.
2. The DP arrays bound `lawKept` only for caps `N > acut` (for small caps `ρ(γ) = ν q^{-γ}` exceeds
   the point mass), which is why the hypotheses are proved at a cap `N ≥ N0` and lifted
   (`hingeLoss_le_of_forall_ge`, `lostMass_le_of_forall_ge`, `lawKept_congr_cap`).
3. Array conventions: `TM` is the largest kept value of `τ` (array size minus one; rigcert's
   `TMAX`). `lawKept_insert` is stated in push form `Σ_{t ≤ TM} Σ_{a ≤ acut q} [t (a+1) = T] D[t] ℓ[a]`,
   matching `dpStep`'s loops (skipped zero entries contribute `0`); `lawKept_insert_pull` is the
   pull form.
4. `fbUp`'s prefix branch needs `k0 = ⌊c⌋ ≤ TM` and `c ≥ 0`; in `gUp`, `c ≥ 1`, and
   `K = ⌊δ(p-1)⌋ + 2 < B.D.size` (`okK`) gives `⌊c⌋ ≤ K`.
5. rigcert's variants (suffix sums, lost-mass recursion, `c < 1` shortcut) are also proved:
   `FB_le_suffix`, `lostMass_insert_le` + `expect1_add_one_le` + `hMass_le_lostThr`,
   `FB_eq_of_le_one`, `GB_diag_le_of`.
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth

/-! ### The whole chain at fixed caps and tilts -/

/-- **The comparison bound** (exact reals, fixed caps `γ` and tilts `ν`): for a partition of
the primes into `A ⊔ B`, `0 ≤ t < 1`, any set `E` of enumerated `A`-configurations, and
`R_k ≥ P(τ_A = k, kept, ∉ E)`, `LA ≥ E[τ_A; lost]`, `EB ≥ E[τ_B]`:
`E[(U_p(s) - t)^+/(1-t)] ≤ (Σ_{a ∈ E} π(a) G(τ_A(a)/(p-1), U_A(a))
   + Σ_{k ≤ KM} R_k G(k/(p-1), k/(p-1)) + LA·EB/(p-1)) / (1-t)`. -/
theorem comparison_bound {p : ℕ} (hp : 1 < p) (m : ℕ) {A B : Finset ℕ} (hAB : Disjoint A B)
    (hA : ∀ q ∈ A, q.Prime) (hB : ∀ q ∈ B, q.Prime) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ A ∪ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (E : (ℕ → ℕ) → Prop) [DecidablePred E] (KM : ℕ) (acut : ℕ → ℕ)
    (R : ℕ → ℝ) (hR : ∀ k ≤ KM, restMass A ν γ KM acut E k ≤ R k)
    (LA : ℝ) (hLA : lostMass A ν γ KM acut ≤ LA) (EB : ℝ) (hEB : meanTau B ν γ ≤ EB) :
    expect (A ∪ B) ν γ (fun v => max 0 (Up p m (smooth (A ∪ B) v) - t) / (1 - t)) ≤
      (∑ a ∈ (box A γ).filter E, weight A ν γ a *
          GB B ν γ t ((tauN A a : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth A a)) +
        ∑ k ∈ range (KM + 1),
          R k * GB B ν γ t ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) +
        LA * EB / ((p : ℝ) - 1)) / (1 - t) := by
  have h1t : 0 < 1 - t := by linarith
  have hνA : ∀ q ∈ A, 0 ≤ ν q ∧ ν q ≤ q := fun q hq => hν q (mem_union_left B hq)
  have hνB : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q := fun q hq => hν q (mem_union_right A hq)
  have e : expect (A ∪ B) ν γ (fun v => max 0 (Up p m (smooth (A ∪ B) v) - t) / (1 - t)) =
      expect (A ∪ B) ν γ (fun v => max 0 (Up p m (smooth (A ∪ B) v) - t)) / (1 - t) := by
    simp only [div_eq_mul_inv]
    exact expect_mul_const _ _
  rw [e]
  exact div_le_div_of_nonneg_right ((expect_hinge_le_split hp m hAB hA hB hν γ t).trans
    (expect_GB_le_enum hp m hA hνA hνB γ ht0 E KM acut R hR LA hLA EB hEB)) h1t.le

/-! ### Connection with `Main.hingeLoss` -/

/-- `hingeLoss` (exact tilts `1/(1 - δ_q)`) is at most the same expectation with any larger
admissible tilts `ν` (e.g. the checker's upward-rounded tilts), with the primes below `p`
written as `A ∪ B`. -/
theorem hingeLoss_le_split_tilt {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime)
    (hδ0 : ∀ q, q.Prime → 0 ≤ δ q) (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, Main.tilt δ q ≤ ν q ∧ ν q ≤ q) {A B : Finset ℕ}
    (hAB : A ∪ B = Nat.primesBelow p) (γ : ℕ → ℕ) :
    Main.hingeLoss m δ p γ ≤
      expect (A ∪ B) ν γ (fun v => max 0 (Up p m (smooth (A ∪ B) v) - δ p) / (1 - δ p)) := by
  have h1 : 0 < 1 - δ p := by linarith [hδ1 p hp]
  have htilt : ∀ q ∈ Nat.primesBelow p, 0 ≤ Main.tilt δ q ∧ Main.tilt δ q ≤ q :=
    fun q hq => Main.tilt_mem hδ0 hδ1 (Nat.prime_of_mem_primesBelow hq)
  have hν' : ∀ q ∈ Nat.primesBelow p, 0 ≤ ν q ∧ ν q ≤ q :=
    fun q hq => ⟨(htilt q hq).1.trans (hν q hq).1, (hν q hq).2⟩
  have hmono : Monotone (fun v =>
      max 0 (Up p m (smooth (Nat.primesBelow p) v) - δ p) / (1 - δ p)) :=
    fun v w hvw => div_le_div_of_nonneg_right
      (monotone_hinge_Up (fun q hq => (Nat.prime_of_mem_primesBelow hq).pos) hp.one_lt m (δ p)
        hvw) h1.le
  unfold Main.hingeLoss
  rw [hAB]
  exact expect_mono_tilt htilt hν' (fun q hq => (hν q hq).1) γ hmono

/-- **The comparison bound for `Main.hingeLoss`** at a fixed cap `γ` (`t = δ_p`). -/
theorem hingeLoss_le_comparison {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime)
    (hδ0 : ∀ q, q.Prime → 0 ≤ δ q) (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, Main.tilt δ q ≤ ν q ∧ ν q ≤ q) {A B : Finset ℕ}
    (hAB : A ∪ B = Nat.primesBelow p) (hdisj : Disjoint A B) (γ : ℕ → ℕ)
    (E : (ℕ → ℕ) → Prop) [DecidablePred E] (KM : ℕ) (acut : ℕ → ℕ)
    (R : ℕ → ℝ) (hR : ∀ k ≤ KM, restMass A ν γ KM acut E k ≤ R k)
    (LA : ℝ) (hLA : lostMass A ν γ KM acut ≤ LA) (EB : ℝ) (hEB : meanTau B ν γ ≤ EB) :
    Main.hingeLoss m δ p γ ≤
      (∑ a ∈ (box A γ).filter E, weight A ν γ a *
          GB B ν γ (δ p) ((tauN A a : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth A a)) +
        ∑ k ∈ range (KM + 1),
          R k * GB B ν γ (δ p) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) +
        LA * EB / ((p : ℝ) - 1)) / (1 - δ p) := by
  have hsub : ∀ q ∈ A ∪ B, q ∈ Nat.primesBelow p := fun q hq => hAB ▸ hq
  have hA : ∀ q ∈ A, q.Prime :=
    fun q hq => Nat.prime_of_mem_primesBelow (hsub q (mem_union_left B hq))
  have hB : ∀ q ∈ B, q.Prime :=
    fun q hq => Nat.prime_of_mem_primesBelow (hsub q (mem_union_right A hq))
  have hνAB : ∀ q ∈ A ∪ B, 0 ≤ ν q ∧ ν q ≤ q := by
    intro q hq
    have hq' := hsub q hq
    have ht := Main.tilt_mem hδ0 hδ1 (Nat.prime_of_mem_primesBelow hq')
    exact ⟨ht.1.trans (hν q hq').1, (hν q hq').2⟩
  exact (hingeLoss_le_split_tilt hp hδ0 hδ1 hν hAB γ).trans
    (comparison_bound hp.one_lt m hdisj hA hB hνAB γ (hδ0 p hp) (by linarith [hδ1 p hp])
      E KM acut R hR LA hLA EB hEB)

/-- **All caps from large caps** (monotone coupling): if `hingeLoss ≤ c` for every uniform cap
`N ≥ N0`, then for every uniform cap. -/
theorem hingeLoss_le_of_forall_ge {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime)
    (hδ0 : ∀ q, q.Prime → 0 ≤ δ q) (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) (N0 : ℕ) {c : ℝ}
    (h : ∀ N, N0 ≤ N → Main.hingeLoss m δ p (fun _ => N) ≤ c) (N : ℕ) :
    Main.hingeLoss m δ p (fun _ => N) ≤ c :=
  (Main.hingeLoss_mono_cap hδ0 hδ1 hp (γ := fun _ => N) (γ' := fun _ => max N N0)
    fun _ _ => le_max_left N N0).trans (h _ (le_max_right N N0))

/-- **The comparison bound, all caps** (the form of `Main.Cert.loss_le` at one prime `p`):
if for every uniform cap `N ≥ N0` there are `R`, `LA`, `EB` bounding the remainder masses, the
lost `τ_A`-mass and `E[τ_B]`, such that the resulting real expression is `≤ cost`, then
`hingeLoss m δ p (fun _ => N) ≤ cost` for **every** `N`. -/
theorem hingeLoss_le_of_comparison {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime)
    (hδ0 : ∀ q, q.Prime → 0 ≤ δ q) (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, Main.tilt δ q ≤ ν q ∧ ν q ≤ q) {A B : Finset ℕ}
    (hAB : A ∪ B = Nat.primesBelow p) (hdisj : Disjoint A B)
    (E : (ℕ → ℕ) → Prop) [DecidablePred E] (KM : ℕ) (acut : ℕ → ℕ) (N0 : ℕ) (cost : ℝ)
    (hcost : ∀ N, N0 ≤ N → ∃ (R : ℕ → ℝ) (LA EB : ℝ),
      (∀ k ≤ KM, restMass A ν (fun _ => N) KM acut E k ≤ R k) ∧
      lostMass A ν (fun _ => N) KM acut ≤ LA ∧ meanTau B ν (fun _ => N) ≤ EB ∧
      (∑ a ∈ (box A (fun _ => N)).filter E, weight A ν (fun _ => N) a *
          GB B ν (fun _ => N) (δ p) ((tauN A a : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth A a)) +
        ∑ k ∈ range (KM + 1), R k *
          GB B ν (fun _ => N) (δ p) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) +
        LA * EB / ((p : ℝ) - 1)) / (1 - δ p) ≤ cost)
    (N : ℕ) : Main.hingeLoss m δ p (fun _ => N) ≤ cost := by
  refine hingeLoss_le_of_forall_ge hp hδ0 hδ1 N0 (fun N hN => ?_) N
  obtain ⟨R, LA, EB, hR, hLA, hEB, hle⟩ := hcost N hN
  exact (hingeLoss_le_comparison hp hδ0 hδ1 hν hAB hdisj (fun _ => N) E KM acut R hR LA hLA
    EB hEB).trans hle

/-! ### Small helpers -/

/-- The A/B partition of `rigcert.c`: `A = {q < p prime, q ≤ z}`, `B` = the rest. -/
theorem primesBelow_filter_union (p z : ℕ) :
    (Nat.primesBelow p).filter (· ≤ z) ∪ (Nat.primesBelow p).filter (fun q => ¬ q ≤ z) =
      Nat.primesBelow p :=
  filter_union_filter_not_eq _ _

theorem primesBelow_filter_disjoint (p z : ℕ) :
    Disjoint ((Nat.primesBelow p).filter (· ≤ z))
      ((Nat.primesBelow p).filter (fun q => ¬ q ≤ z)) :=
  disjoint_filter_filter_not _ _ _

/-- An empty B part (`31 ≤ p ≤ 47` in rigcert's split): `τ_B = 1`. -/
theorem meanTau_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) : meanTau ∅ ν γ = 1 := by
  simp [meanTau]

theorem GB_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (t α u : ℝ) : GB ∅ ν γ t α u = max 0 (u - t) := by
  simp [GB]

end MinModulus.CheckerMath
