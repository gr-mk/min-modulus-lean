import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Distortion measures (BBMST), full-space formulation

STATUS: complete. No `sorry`; every theorem depends only on `propext`, `Classical.choice`,
`Quot.sound`. Imports: Mathlib only.

## Setting
* `X : Fin n → Type*`, each a `Fintype` with `DecidableEq`; the space is
  `Ω = (j : Fin n) → X j` and `N_j = Fintype.card (X j)`.
* `B : Fin n → Finset Ω`, with hypothesis `DependsLE B`: membership in `B ℓ` depends only on
  the coordinates `≤ ℓ`.
* `δ : Fin n → ℝ` with `0 ≤ δ ℓ < 1`.

## Definitions
* `alpha B ℓ x = #{y ∈ X ℓ | update x ℓ y ∈ B ℓ} / N_ℓ` (BBMST (4)); depends only on the
  coordinates `< ℓ` (`alpha_congr`), and not at all on coordinate `ℓ` (`alpha_update_self`).
* `factor B δ ℓ x` is BBMST (5):
  `if x ∈ B ℓ then (if α = 0 then 0 else max 0 ((α - δ)/(α(1 - δ))))`
  `else min (1/(1 - α)) (1/(1 - δ))`. It depends only on the coordinates `≤ ℓ`
  (`factor_congr`).
* `P B δ m x = (∏_{j : j.val < m} factor B δ j x) / card Ω`. So `P 0` is uniform, unprocessed
  coordinates stay uniform, and `P m = P n` for `m ≥ n` (`P_of_le`). No prefix spaces.
* `kernel B δ m j x y = (if j < m then factor B δ j (update x j y) else 1) / N_j` and
  `nu δ m j = if j < m then 1/(1 - δ j) else 1`.

## Main results
* (F0) `P_nonneg`, `sum_P`.
* (F1) `sum_P_succ_mul`.
* (F2) `factor_nonneg`, `factor_le`.
* (F3) `sum_mem_P_succ`.
* (F4) `exists_forall_not_mem` (via `sum_mem_P_eq`: `P n (B ℓ) = P (ℓ+1) (B ℓ)`).
* Kernel form: `P_eq_prod_kernel`, `kernel_nonneg`, `kernel_sum`, `kernel_le`, `one_le_nu`,
  `kernel_dep` (the exact shape of the hypotheses `hK0 hK1 hKν hν hKdep` of
  `Comparison.comparison`, with `K = kernel B δ m`, `ν = nu δ m`).
* Exported criterion: `criterion`; variant `criterion_kernel` (pointwise majorant, kernel form).
* Edge cases: `factor_of_alpha_eq_zero`, `factor_of_alpha_eq_one`, `factor_of_delta_eq_zero`,
  `P_succ_of_delta_eq_zero`, `loss_of_delta_eq_zero` (loss `= E_{P ℓ}[α ℓ]` when `δ ℓ = 0`),
  and the two regimes `factor_of_(not_)mem_of_alpha_le`, `factor_of_(not_)mem_of_lt_alpha`.

## Summing over one coordinate of the dependent product
We never split `Ω`. The single tool is the involution `(x, y) ↦ (update x ℓ y, x ℓ)` of
`Ω × X ℓ` (`sum_sum_update_swap`, via `Function.Involutive.bijective` and
`Fintype.sum_prod_type'`). It gives `∑ x, ∑ y, G (update x ℓ y) = N_ℓ * ∑ x, G x`
(`sum_sum_update`), hence fibre averaging (`sum_mul_eq_of_fibre`): if `A` does not depend on
coordinate `ℓ` and the fibre sums of `C` are `N_ℓ · D`, then `∑ A C = ∑ A D`. (F1) and (F3)
are this lemma plus the one-fibre identities `sum_factor_update` (fibre sum of the factor is
`N_ℓ`, BBMST Lemma 2.1) and `sum_mem_factor_update` (fibre sum over `B ℓ` is
`N_ℓ · (α - δ)⁺/(1 - δ)`), whose algebraic cores are `fibre_aux` and `loss_aux`.

## Conventions and deviations from LEAN_DESIGN.md
* `P` is indexed by `m : ℕ`. For `ℓ : Fin n`, "`P ℓ`" is `P B δ ℓ` (coercion to `ℕ`) and
  "`P (ℓ+1)`" is `P B δ ((ℓ : ℕ) + 1)`.
* `B` is a `Finset`; its dependence hypothesis is the `Prop` `DependsLE B`.
* `[∀ j, Nonempty (X j)]` is assumed only where it is needed: `sum_P`, `exists_forall_not_mem`,
  `criterion`, `criterion_kernel` (all other results hold without it).
* The guard `if α = 0 then 0` in the factor is unreachable for `x ∈ B ℓ` (`alpha_pos_of_mem`);
  it only keeps the literal formula total.
-/

namespace MinModulus.Distortion

open Finset Function

variable {n : ℕ} {X : Fin n → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- `B ℓ` depends only on the coordinates `≤ ℓ`. -/
def DependsLE (B : Fin n → Finset ((j : Fin n) → X j)) : Prop :=
  ∀ (ℓ : Fin n) (x x' : (j : Fin n) → X j), (∀ j, j ≤ ℓ → x j = x' j) → (x ∈ B ℓ ↔ x' ∈ B ℓ)

section Defs

variable (B : Fin n → Finset ((j : Fin n) → X j)) (δ : Fin n → ℝ)

/-- `α ℓ x`: the proportion of the fibre of `x` in direction `ℓ` that lies in `B ℓ`. -/
noncomputable def alpha (ℓ : Fin n) (x : (j : Fin n) → X j) : ℝ :=
  ((univ.filter (fun y : X ℓ => update x ℓ y ∈ B ℓ)).card : ℝ) / (Fintype.card (X ℓ) : ℝ)

/-- The BBMST distortion factor at level `ℓ` (formula (5) of BBMST). -/
noncomputable def factor (ℓ : Fin n) (x : (j : Fin n) → X j) : ℝ :=
  if x ∈ B ℓ then
    (if alpha B ℓ x = 0 then 0
      else max 0 ((alpha B ℓ x - δ ℓ) / (alpha B ℓ x * (1 - δ ℓ))))
  else min (1 / (1 - alpha B ℓ x)) (1 / (1 - δ ℓ))

/-- The measure after the first `m` levels have been processed. -/
noncomputable def P (m : ℕ) (x : (j : Fin n) → X j) : ℝ :=
  (∏ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < m), factor B δ j x) /
    (Fintype.card ((j : Fin n) → X j) : ℝ)

/-- Kernel form of `P m`. -/
noncomputable def kernel (m : ℕ) (j : Fin n) (x : (i : Fin n) → X i) (y : X j) : ℝ :=
  (if (j : ℕ) < m then factor B δ j (update x j y) else 1) / (Fintype.card (X j) : ℝ)

/-- The tilt bounds for `kernel m`. -/
noncomputable def nu (m : ℕ) (j : Fin n) : ℝ :=
  if (j : ℕ) < m then 1 / (1 - δ j) else 1

end Defs

/-! ### Summation over one coordinate -/

section Fibre

omit [∀ j, DecidableEq (X j)] in
/-- The involution `(x, y) ↦ (update x ℓ y, x ℓ)` of `Ω × X ℓ` exchanges the two sums. -/
theorem sum_sum_update_swap {M : Type*} [AddCommMonoid M] (ℓ : Fin n)
    (F : ((j : Fin n) → X j) → X ℓ → M) :
    ∑ x, ∑ y, F x y = ∑ x, ∑ y, F (update x ℓ y) (x ℓ) := by
  have hs : Function.Involutive
      (fun p : ((j : Fin n) → X j) × X ℓ => (update p.1 ℓ p.2, p.1 ℓ)) := by
    rintro ⟨x, y⟩
    simp only [update_idem, update_eq_self, update_self]
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact (hs.bijective.sum_comp (fun p => F p.1 p.2)).symm

omit [∀ j, DecidableEq (X j)] in
/-- Summing a function over all the points of every fibre in direction `ℓ`. -/
theorem sum_sum_update (ℓ : Fin n) (G : ((j : Fin n) → X j) → ℝ) :
    ∑ x, ∑ y : X ℓ, G (update x ℓ y) = (Fintype.card (X ℓ) : ℝ) * ∑ x, G x := by
  rw [sum_sum_update_swap ℓ (fun x y => G (update x ℓ y))]
  simp only [update_idem, update_eq_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.mul_sum]

omit [∀ j, DecidableEq (X j)] in
/-- Fibre averaging: if `A` is constant on the fibres in direction `ℓ` and the fibre sums of
`C` are `N_ℓ · D`, then `∑ A C = ∑ A D`. -/
theorem sum_mul_eq_of_fibre (ℓ : Fin n) (A C D : ((j : Fin n) → X j) → ℝ)
    (hA : ∀ x y, A (update x ℓ y) = A x)
    (hCD : ∀ x, ∑ y, C (update x ℓ y) = (Fintype.card (X ℓ) : ℝ) * D x) :
    ∑ x, A x * C x = ∑ x, A x * D x := by
  rcases isEmpty_or_nonempty (X ℓ) with hX | hX
  · have : IsEmpty ((j : Fin n) → X j) := ⟨fun x => hX.false (x ℓ)⟩
    simp [Finset.univ_eq_empty]
  have hN : (Fintype.card (X ℓ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  apply mul_left_cancel₀ hN
  calc (Fintype.card (X ℓ) : ℝ) * ∑ x, A x * C x
      = ∑ x, ∑ y, A (update x ℓ y) * C (update x ℓ y) := (sum_sum_update ℓ _).symm
    _ = ∑ x, A x * ∑ y, C (update x ℓ y) := by simp only [hA, Finset.mul_sum]
    _ = ∑ x, A x * ((Fintype.card (X ℓ) : ℝ) * D x) := by simp only [hCD]
    _ = (Fintype.card (X ℓ) : ℝ) * ∑ x, A x * D x := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)

end Fibre

variable {B : Fin n → Finset ((j : Fin n) → X j)} {δ : Fin n → ℝ}

/-! ### Basic properties of `α` -/

section Alpha

omit [∀ j, DecidableEq (X j)] in
theorem card_pos_of_point (ℓ : Fin n) (x : (j : Fin n) → X j) :
    (0 : ℝ) < Fintype.card (X ℓ) :=
  Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x ℓ⟩)

theorem alpha_update_self (ℓ : Fin n) (x : (j : Fin n) → X j) (y : X ℓ) :
    alpha B ℓ (update x ℓ y) = alpha B ℓ x := by
  simp only [alpha, update_idem]

theorem alpha_nonneg (ℓ : Fin n) (x : (j : Fin n) → X j) : 0 ≤ alpha B ℓ x := by
  unfold alpha; positivity

theorem alpha_le_one (ℓ : Fin n) (x : (j : Fin n) → X j) : alpha B ℓ x ≤ 1 := by
  unfold alpha
  rw [div_le_one (card_pos_of_point ℓ x)]
  exact_mod_cast (Finset.card_filter_le _ _).trans_eq Finset.card_univ

theorem alpha_pos_of_mem {ℓ : Fin n} {x : (j : Fin n) → X j} (hx : x ∈ B ℓ) :
    0 < alpha B ℓ x := by
  unfold alpha
  apply div_pos _ (card_pos_of_point ℓ x)
  have : x ℓ ∈ univ.filter (fun y : X ℓ => update x ℓ y ∈ B ℓ) := by
    simp only [Finset.mem_filter, Finset.mem_univ, update_eq_self, true_and, hx]
  exact_mod_cast Finset.card_pos.mpr ⟨x ℓ, this⟩

theorem alpha_lt_one_of_not_mem {ℓ : Fin n} {x : (j : Fin n) → X j} (hx : x ∉ B ℓ) :
    alpha B ℓ x < 1 := by
  unfold alpha
  rw [div_lt_one (card_pos_of_point ℓ x)]
  have : univ.filter (fun y : X ℓ => update x ℓ y ∈ B ℓ) ⊂ univ := by
    rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
    exact ⟨x ℓ, Finset.mem_univ _, by simp only [Finset.mem_filter, update_eq_self, hx,
      and_false, not_false_eq_true]⟩
  exact_mod_cast (Finset.card_lt_card this).trans_eq Finset.card_univ

/-- `α ℓ` depends only on the coordinates `< ℓ`. -/
theorem alpha_congr (hB : DependsLE B) {ℓ : Fin n} {x x' : (j : Fin n) → X j}
    (h : ∀ j, j < ℓ → x j = x' j) : alpha B ℓ x = alpha B ℓ x' := by
  have hset : univ.filter (fun y : X ℓ => update x ℓ y ∈ B ℓ)
      = univ.filter (fun y : X ℓ => update x' ℓ y ∈ B ℓ) := by
    apply Finset.filter_congr
    intro y _
    apply hB ℓ
    intro j hj
    rcases hj.lt_or_eq with hlt | rfl
    · rw [update_of_ne hlt.ne, update_of_ne hlt.ne]; exact h j hlt
    · simp only [update_self]
  unfold alpha
  rw [hset]

end Alpha

/-! ### The factor -/

section Factor

/-- `f ℓ` depends only on the coordinates `≤ ℓ`. -/
theorem factor_congr (hB : DependsLE B) {ℓ : Fin n} {x x' : (j : Fin n) → X j}
    (h : ∀ j, j ≤ ℓ → x j = x' j) : factor B δ ℓ x = factor B δ ℓ x' := by
  have hα : alpha B ℓ x = alpha B ℓ x' := alpha_congr hB (fun j hj => h j hj.le)
  have hmem : x ∈ B ℓ ↔ x' ∈ B ℓ := hB ℓ x x' h
  unfold factor
  rw [hα]
  by_cases hx : x ∈ B ℓ
  · rw [ite_eq_left hx, ite_eq_left (hmem.mp hx)]
  · rw [ite_eq_right hx, ite_eq_right (fun h' => hx (hmem.mpr h'))]

theorem factor_update_of_lt (hB : DependsLE B) {j i : Fin n} (hji : j < i)
    (x : (j : Fin n) → X j) (y : X i) : factor B δ j (update x i y) = factor B δ j x :=
  factor_congr hB (fun _ hk => update_of_ne (lt_of_le_of_lt hk hji).ne y x)

/-- (F2), lower bound. -/
theorem factor_nonneg {ℓ : Fin n} (hδ1 : δ ℓ < 1) (x : (j : Fin n) → X j) :
    0 ≤ factor B δ ℓ x := by
  have hα := alpha_le_one (B := B) ℓ x
  unfold factor
  split_ifs with h1 h2
  · exact le_rfl
  · exact le_max_left _ _
  · apply le_min
    · exact div_nonneg zero_le_one (by linarith)
    · exact div_nonneg zero_le_one (by linarith)

/-- (F2), upper bound. -/
theorem factor_le {ℓ : Fin n} (hδ0 : 0 ≤ δ ℓ) (hδ1 : δ ℓ < 1) (x : (j : Fin n) → X j) :
    factor B δ ℓ x ≤ 1 / (1 - δ ℓ) := by
  have hd : 0 < 1 - δ ℓ := by linarith
  unfold factor
  split_ifs with h1 h2
  · positivity
  · apply max_le (by positivity)
    have ha : 0 < alpha B ℓ x := alpha_pos_of_mem h1
    rw [div_le_div_iff₀ (by positivity) hd]
    nlinarith
  · exact min_le_right _ _

/-- Algebraic core of the fibre identity: `a·f_in(a) + (1 - a)·f_out(a) = 1`. -/
theorem fibre_aux {a d : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    a * (if a = 0 then 0 else max 0 ((a - d) / (a * (1 - d))))
      + (1 - a) * min (1 / (1 - a)) (1 / (1 - d)) = 1 := by
  have hd' : 0 < 1 - d := by linarith
  rcases ha0.eq_or_lt with rfl | ha
  · rw [ite_eq_left rfl, mul_zero, zero_add, sub_zero, one_mul, div_one]
    exact min_eq_left (one_le_one_div hd' (by linarith))
  · rw [ite_eq_right ha.ne']
    rcases ha1.eq_or_lt with rfl | ha1'
    · rw [sub_self, zero_mul, add_zero, one_mul, one_mul, div_self hd'.ne']
      exact max_eq_right zero_le_one
    · have ha' : a ≠ 0 := ha.ne'
      have hd'' : 1 - d ≠ 0 := hd'.ne'
      have h1a : 1 - a ≠ 0 := by linarith
      rcases le_or_gt a d with had | had
      · have h1 : (a - d) / (a * (1 - d)) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        rw [max_eq_left h1, min_eq_left (one_div_le_one_div_of_le hd' (by linarith)),
          mul_zero, zero_add, mul_one_div_cancel h1a]
      · have h1 : 0 ≤ (a - d) / (a * (1 - d)) := div_nonneg (by linarith) (by positivity)
        rw [max_eq_right h1, min_eq_right (one_div_le_one_div_of_le (by linarith) (by linarith))]
        field_simp
        ring

/-- Algebraic core of the loss identity: `a·f_in(a) = (a - d)⁺/(1 - d)`. -/
theorem loss_aux {a d : ℝ} (ha0 : 0 ≤ a) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    a * (if a = 0 then 0 else max 0 ((a - d) / (a * (1 - d))))
      = max 0 (a - d) / (1 - d) := by
  have hd' : 0 < 1 - d := by linarith
  rcases ha0.eq_or_lt with rfl | ha
  · rw [ite_eq_left rfl, mul_zero, zero_sub, max_eq_left (by linarith), zero_div]
  · rw [ite_eq_right ha.ne', ← max_div_div_right hd'.le, mul_max_of_nonneg _ _ ha.le, mul_zero,
      zero_div, mul_div_assoc', mul_div_mul_left _ _ ha.ne']

/-! #### Edge cases and the two regimes of the factor -/

/-- `α = 0`: the fibre misses `B ℓ`, and the factor is `1` (no distortion). -/
theorem factor_of_alpha_eq_zero {ℓ : Fin n} (hδ0 : 0 ≤ δ ℓ) (hδ1 : δ ℓ < 1)
    {x : (j : Fin n) → X j} (hα : alpha B ℓ x = 0) : factor B δ ℓ x = 1 := by
  have hx : x ∉ B ℓ := fun hx => (alpha_pos_of_mem hx).ne' hα
  rw [factor, ite_eq_right hx, hα, sub_zero, div_one]
  exact min_eq_left (one_le_one_div (by linarith) (by linarith))

/-- `α = 1`: the fibre lies inside `B ℓ`, and the factor is `1` (no distortion). -/
theorem factor_of_alpha_eq_one {ℓ : Fin n} (hδ1 : δ ℓ < 1) {x : (j : Fin n) → X j}
    (hα : alpha B ℓ x = 1) : factor B δ ℓ x = 1 := by
  have hx : x ∈ B ℓ := by
    by_contra hx
    exact (alpha_lt_one_of_not_mem hx).ne hα
  rw [factor, ite_eq_left hx, hα, ite_eq_right one_ne_zero, one_mul,
    div_self (by linarith : (1 : ℝ) - δ ℓ ≠ 0)]
  exact max_eq_right zero_le_one

/-- `δ = 0`: the factor is identically `1`. -/
theorem factor_of_delta_eq_zero {ℓ : Fin n} (hδ : δ ℓ = 0) (x : (j : Fin n) → X j) :
    factor B δ ℓ x = 1 := by
  have h0 := alpha_nonneg (B := B) ℓ x
  unfold factor
  rw [hδ]
  split_ifs with h1 h2
  · exact absurd h2 (alpha_pos_of_mem h1).ne'
  · rw [sub_zero, sub_zero, mul_one, div_self (alpha_pos_of_mem h1).ne']
    exact max_eq_right zero_le_one
  · have h3 := alpha_lt_one_of_not_mem h1
    rw [sub_zero, div_one]
    exact min_eq_right (one_le_one_div (by linarith) (by linarith))

/-- Regime `α ≤ δ`, point of `B ℓ`: the point is killed. -/
theorem factor_of_mem_of_alpha_le {ℓ : Fin n} (hδ1 : δ ℓ < 1) {x : (j : Fin n) → X j}
    (hx : x ∈ B ℓ) (h : alpha B ℓ x ≤ δ ℓ) : factor B δ ℓ x = 0 := by
  have ha := alpha_pos_of_mem hx
  have hd : 0 < 1 - δ ℓ := by linarith
  rw [factor, ite_eq_left hx, ite_eq_right ha.ne']
  exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))

/-- Regime `α ≤ δ`, point outside `B ℓ`: boosted by `1/(1 - α)`. -/
theorem factor_of_not_mem_of_alpha_le {ℓ : Fin n} (hδ1 : δ ℓ < 1) {x : (j : Fin n) → X j}
    (hx : x ∉ B ℓ) (h : alpha B ℓ x ≤ δ ℓ) : factor B δ ℓ x = 1 / (1 - alpha B ℓ x) := by
  rw [factor, ite_eq_right hx]
  exact min_eq_left (one_div_le_one_div_of_le (by linarith) (by linarith))

/-- Regime `α > δ`, point of `B ℓ`: scaled by `(α - δ)/(α(1 - δ))`. -/
theorem factor_of_mem_of_lt_alpha {ℓ : Fin n} (hδ1 : δ ℓ < 1) {x : (j : Fin n) → X j}
    (hx : x ∈ B ℓ) (h : δ ℓ < alpha B ℓ x) :
    factor B δ ℓ x = (alpha B ℓ x - δ ℓ) / (alpha B ℓ x * (1 - δ ℓ)) := by
  have ha := alpha_pos_of_mem hx
  have hd : 0 < 1 - δ ℓ := by linarith
  rw [factor, ite_eq_left hx, ite_eq_right ha.ne']
  exact max_eq_right (div_nonneg (by linarith) (by positivity))

/-- Regime `α > δ`, point outside `B ℓ`: boosted by the cap `1/(1 - δ)`. -/
theorem factor_of_not_mem_of_lt_alpha {ℓ : Fin n} {x : (j : Fin n) → X j}
    (hx : x ∉ B ℓ) (h : δ ℓ < alpha B ℓ x) : factor B δ ℓ x = 1 / (1 - δ ℓ) := by
  have h1 := alpha_lt_one_of_not_mem hx
  rw [factor, ite_eq_right hx]
  exact min_eq_right (one_div_le_one_div_of_le (by linarith) (by linarith))

end Factor

/-! ### Fibre sums of the factor -/

section FibreSums

theorem sum_ite_update (ℓ : Fin n) (x : (j : Fin n) → X j) (u v : ℝ) :
    ∑ y : X ℓ, (if update x ℓ y ∈ B ℓ then u else v)
      = (Fintype.card (X ℓ) : ℝ) * (alpha B ℓ x * u + (1 - alpha B ℓ x) * v) := by
  have hN : (Fintype.card (X ℓ) : ℝ) ≠ 0 := (card_pos_of_point ℓ x).ne'
  have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (X ℓ)))
    (fun y => update x ℓ y ∈ B ℓ)
  rw [Finset.card_univ] at hc
  have hk : ((univ.filter (fun y : X ℓ => ¬ update x ℓ y ∈ B ℓ)).card : ℝ)
      = (Fintype.card (X ℓ) : ℝ) - (univ.filter (fun y : X ℓ => update x ℓ y ∈ B ℓ)).card := by
    rw [← hc]; push_cast; ring
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hk]
  unfold alpha
  field_simp

/-- The fibre identity: the factor has average `1` on every fibre (BBMST Lemma 2.1). -/
theorem sum_factor_update (ℓ : Fin n) (hδ0 : 0 ≤ δ ℓ) (hδ1 : δ ℓ < 1)
    (x : (j : Fin n) → X j) :
    ∑ y : X ℓ, factor B δ ℓ (update x ℓ y) = Fintype.card (X ℓ) := by
  simp only [factor, alpha_update_self]
  rw [sum_ite_update, fibre_aux (alpha_nonneg ℓ x) (alpha_le_one ℓ x) hδ0 hδ1, mul_one]

/-- The loss identity on one fibre. -/
theorem sum_mem_factor_update (ℓ : Fin n) (hδ0 : 0 ≤ δ ℓ) (hδ1 : δ ℓ < 1)
    (x : (j : Fin n) → X j) :
    ∑ y : X ℓ, (if update x ℓ y ∈ B ℓ then factor B δ ℓ (update x ℓ y) else 0)
      = (Fintype.card (X ℓ) : ℝ) * (max 0 (alpha B ℓ x - δ ℓ) / (1 - δ ℓ)) := by
  have e : ∀ y : X ℓ, (if update x ℓ y ∈ B ℓ then factor B δ ℓ (update x ℓ y) else 0)
      = if update x ℓ y ∈ B ℓ then
          (if alpha B ℓ x = 0 then 0
            else max 0 ((alpha B ℓ x - δ ℓ) / (alpha B ℓ x * (1 - δ ℓ)))) else 0 := by
    intro y
    by_cases h : update x ℓ y ∈ B ℓ
    · rw [ite_eq_left h, ite_eq_left h, factor, ite_eq_left h, alpha_update_self]
    · rw [ite_eq_right h, ite_eq_right h]
  simp only [e]
  rw [sum_ite_update, mul_zero, add_zero, loss_aux (alpha_nonneg ℓ x) hδ0 hδ1]

end FibreSums

/-! ### The measures `P m` -/

section Measure

theorem P_zero (x : (j : Fin n) → X j) :
    P B δ 0 x = 1 / (Fintype.card ((j : Fin n) → X j) : ℝ) := by
  simp [P]

theorem P_succ (ℓ : Fin n) (x : (j : Fin n) → X j) :
    P B δ ((ℓ : ℕ) + 1) x = P B δ ℓ x * factor B δ ℓ x := by
  have hset : univ.filter (fun j : Fin n => (j : ℕ) < (ℓ : ℕ) + 1)
      = insert ℓ (univ.filter (fun j : Fin n => (j : ℕ) < ℓ)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : ℓ ∉ univ.filter (fun j : Fin n => (j : ℕ) < ℓ) := by simp
  unfold P
  rw [hset, Finset.prod_insert hnot]
  ring

theorem P_of_le {m : ℕ} (hm : n ≤ m) (x : (j : Fin n) → X j) : P B δ m x = P B δ n x := by
  unfold P
  have : univ.filter (fun j : Fin n => (j : ℕ) < m)
      = univ.filter (fun j : Fin n => (j : ℕ) < n) := by
    apply Finset.filter_congr
    intro j _
    have := j.isLt
    omega
  rw [this]

theorem P_nonneg (hδ1 : ∀ ℓ, δ ℓ < 1) (m : ℕ) (x : (j : Fin n) → X j) :
    0 ≤ P B δ m x := by
  unfold P
  apply div_nonneg
  · exact Finset.prod_nonneg (fun j _ => factor_nonneg (hδ1 j) x)
  · positivity

/-- `P m` depends only on the coordinates `< m`. -/
theorem P_update (hB : DependsLE B) {m : ℕ} {i : Fin n} (hi : m ≤ (i : ℕ))
    (x : (j : Fin n) → X j) (y : X i) : P B δ m (update x i y) = P B δ m x := by
  unfold P
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Finset.mem_filter] at hj
  exact factor_update_of_lt hB (Fin.lt_def.mpr (by omega)) x y

/-- (F1) -/
theorem sum_P_succ_mul (hB : DependsLE B) {ℓ : Fin n} (hδ0 : 0 ≤ δ ℓ) (hδ1 : δ ℓ < 1)
    (g : ((j : Fin n) → X j) → ℝ) (hg : ∀ x y, g (update x ℓ y) = g x) :
    ∑ x, P B δ ((ℓ : ℕ) + 1) x * g x = ∑ x, P B δ ℓ x * g x := by
  have h := sum_mul_eq_of_fibre ℓ (fun x => P B δ ℓ x * g x) (factor B δ ℓ) (fun _ => 1)
    (fun x y => by simp only [P_update hB le_rfl, hg])
    (fun x => by rw [sum_factor_update ℓ hδ0 hδ1, mul_one])
  simp only [mul_one] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [P_succ]; ring

/-- (F0) -/
theorem sum_P [∀ j, Nonempty (X j)] (hB : DependsLE B) (hδ0 : ∀ ℓ, 0 ≤ δ ℓ)
    (hδ1 : ∀ ℓ, δ ℓ < 1) (m : ℕ) : ∑ x, P B δ m x = 1 := by
  induction m with
  | zero =>
    simp only [P_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card ((j : Fin n) → X j) := by exact_mod_cast Fintype.card_pos
    field_simp
  | succ m ih =>
    by_cases hmn : m < n
    · have key := sum_P_succ_mul hB (ℓ := ⟨m, hmn⟩) (hδ0 _) (hδ1 _) (fun _ => 1)
        (fun _ _ => rfl)
      simp only [mul_one] at key
      exact key.trans ih
    · have e : ∀ x, P B δ (m + 1) x = P B δ m x := fun x => by
        rw [P_of_le (m := m + 1) (by omega), P_of_le (m := m) (by omega)]
      simp only [e]
      exact ih

/-- (F3) -/
theorem sum_mem_P_succ (hB : DependsLE B) {ℓ : Fin n} (hδ0 : 0 ≤ δ ℓ) (hδ1 : δ ℓ < 1) :
    ∑ x ∈ B ℓ, P B δ ((ℓ : ℕ) + 1) x
      = ∑ x, P B δ ℓ x * (max 0 (alpha B ℓ x - δ ℓ) / (1 - δ ℓ)) := by
  have h := sum_mul_eq_of_fibre ℓ (P B δ ℓ) (fun x => if x ∈ B ℓ then factor B δ ℓ x else 0)
    (fun x => max 0 (alpha B ℓ x - δ ℓ) / (1 - δ ℓ))
    (fun x y => P_update hB le_rfl x y)
    (fun x => sum_mem_factor_update ℓ hδ0 hδ1 x)
  rw [← h, ← Finset.sum_ite_mem_eq (B ℓ)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [P_succ]
  split_ifs <;> ring

/-- Once level `ℓ` has been processed, the mass of `B ℓ` no longer changes. -/
theorem sum_mem_P_eq (hB : DependsLE B) (hδ0 : ∀ ℓ, 0 ≤ δ ℓ) (hδ1 : ∀ ℓ, δ ℓ < 1)
    (ℓ : Fin n) (m : ℕ) (hm : (ℓ : ℕ) + 1 ≤ m) :
    ∑ x ∈ B ℓ, P B δ m x = ∑ x ∈ B ℓ, P B δ ((ℓ : ℕ) + 1) x := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [← ih]
    by_cases hmn : m < n
    · have hli : ℓ < (⟨m, hmn⟩ : Fin n) := Fin.lt_def.mpr (by simp only; omega)
      have key := sum_P_succ_mul hB (ℓ := ⟨m, hmn⟩) (hδ0 _) (hδ1 _)
        (fun x => if x ∈ B ℓ then (1 : ℝ) else 0)
        (fun x y => by
          have : update x ⟨m, hmn⟩ y ∈ B ℓ ↔ x ∈ B ℓ :=
            hB ℓ _ _ (fun j hj => update_of_ne (lt_of_le_of_lt hj hli).ne y x)
          simp only [this])
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem_eq] at key
      exact key
    · have e : ∀ x, P B δ (m + 1) x = P B δ m x := fun x => by
        rw [P_of_le (m := m + 1) (by omega), P_of_le (m := m) (by omega)]
      simp only [e]

/-- (F4) -/
theorem exists_forall_not_mem [∀ j, Nonempty (X j)] (hB : DependsLE B)
    (hδ0 : ∀ ℓ, 0 ≤ δ ℓ) (hδ1 : ∀ ℓ, δ ℓ < 1)
    (h : ∑ ℓ : Fin n, ∑ x ∈ B ℓ, P B δ ((ℓ : ℕ) + 1) x < 1) :
    ∃ x : (j : Fin n) → X j, ∀ ℓ, x ∉ B ℓ := by
  by_contra hcon
  simp only [not_exists, not_forall, not_not] at hcon
  have h1 : ∑ x, P B δ n x = 1 := sum_P hB hδ0 hδ1 n
  have e : ∀ ℓ : Fin n, ∑ x ∈ B ℓ, P B δ n x = ∑ x, if x ∈ B ℓ then P B δ n x else 0 :=
    fun ℓ => (Finset.sum_ite_mem_eq (B ℓ) _).symm
  have h2 : ∑ x, P B δ n x ≤ ∑ ℓ : Fin n, ∑ x ∈ B ℓ, P B δ n x := by
    rw [Finset.sum_congr rfl (fun ℓ _ => e ℓ), Finset.sum_comm]
    refine Finset.sum_le_sum (fun x _ => ?_)
    obtain ⟨ℓ₀, hℓ₀⟩ := hcon x
    have := Finset.single_le_sum (f := fun ℓ => if x ∈ B ℓ then P B δ n x else 0)
      (fun ℓ _ => by
        by_cases hx : x ∈ B ℓ
        · simp only [hx, ite_true]; exact P_nonneg hδ1 n x
        · simp only [hx, ite_false]; exact le_rfl)
      (Finset.mem_univ ℓ₀)
    simpa only [hℓ₀, ite_true] using this
  have h3 : ∀ ℓ : Fin n, ∑ x ∈ B ℓ, P B δ n x = ∑ x ∈ B ℓ, P B δ ((ℓ : ℕ) + 1) x :=
    fun ℓ => sum_mem_P_eq hB hδ0 hδ1 ℓ n ℓ.isLt
  simp only [h3] at h2
  linarith

/-- `δ ℓ = 0`: level `ℓ` does not distort, `P (ℓ+1) = P ℓ` (in particular on `B ℓ`). -/
theorem P_succ_of_delta_eq_zero {ℓ : Fin n} (hδ : δ ℓ = 0) (x : (j : Fin n) → X j) :
    P B δ ((ℓ : ℕ) + 1) x = P B δ ℓ x := by
  rw [P_succ, factor_of_delta_eq_zero hδ, mul_one]

/-- `δ ℓ = 0`: the loss at level `ℓ` is `E_{P ℓ}[α ℓ]`. -/
theorem loss_of_delta_eq_zero (hB : DependsLE B) {ℓ : Fin n} (hδ : δ ℓ = 0) :
    ∑ x ∈ B ℓ, P B δ ((ℓ : ℕ) + 1) x = ∑ x, P B δ ℓ x * alpha B ℓ x := by
  rw [sum_mem_P_succ hB (le_of_eq hδ.symm) (by rw [hδ]; exact zero_lt_one)]
  have e : ∀ x, max 0 (alpha B ℓ x - δ ℓ) / (1 - δ ℓ) = alpha B ℓ x := fun x => by
    rw [hδ, sub_zero, sub_zero, div_one, max_eq_right (alpha_nonneg ℓ x)]
  simp only [e]

end Measure

/-! ### Kernel form -/

section Kernel

theorem P_eq_prod_kernel (m : ℕ) (x : (j : Fin n) → X j) :
    P B δ m x = ∏ j, kernel B δ m j x (x j) := by
  simp only [kernel, update_eq_self, Finset.prod_div_distrib, P, Finset.prod_filter,
    Fintype.card_pi, Nat.cast_prod]

theorem kernel_nonneg (hδ1 : ∀ ℓ, δ ℓ < 1) (m : ℕ) (j : Fin n) (x : (i : Fin n) → X i)
    (y : X j) : 0 ≤ kernel B δ m j x y := by
  unfold kernel
  apply div_nonneg _ (Nat.cast_nonneg _)
  split_ifs
  · exact factor_nonneg (hδ1 j) _
  · exact zero_le_one

theorem kernel_sum (hδ0 : ∀ ℓ, 0 ≤ δ ℓ) (hδ1 : ∀ ℓ, δ ℓ < 1) (m : ℕ) (j : Fin n)
    (x : (i : Fin n) → X i) : ∑ y, kernel B δ m j x y = 1 := by
  have hN : (Fintype.card (X j) : ℝ) ≠ 0 := (card_pos_of_point j x).ne'
  unfold kernel
  rw [← Finset.sum_div]
  by_cases h : (j : ℕ) < m
  · simp only [h, ite_true]
    rw [sum_factor_update j (hδ0 j) (hδ1 j) x, div_self hN]
  · simp only [h, ite_false]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_self hN]

theorem kernel_le (hδ0 : ∀ ℓ, 0 ≤ δ ℓ) (hδ1 : ∀ ℓ, δ ℓ < 1) (m : ℕ) (j : Fin n)
    (x : (i : Fin n) → X i) (y : X j) :
    kernel B δ m j x y ≤ nu δ m j / (Fintype.card (X j) : ℝ) := by
  unfold kernel nu
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  split_ifs
  · exact factor_le (hδ0 j) (hδ1 j) _
  · exact le_rfl

theorem one_le_nu (hδ0 : ∀ ℓ, 0 ≤ δ ℓ) (hδ1 : ∀ ℓ, δ ℓ < 1) (m : ℕ) (j : Fin n) :
    1 ≤ nu δ m j := by
  unfold nu
  split_ifs
  · exact one_le_one_div (by linarith [hδ1 j]) (by linarith [hδ0 j])
  · exact le_rfl

theorem kernel_congr (hB : DependsLE B) (m : ℕ) (j : Fin n) {x x' : (i : Fin n) → X i}
    (h : ∀ i, i < j → x i = x' i) (y : X j) :
    kernel B δ m j x y = kernel B δ m j x' y := by
  have e : factor B δ j (update x j y) = factor B δ j (update x' j y) := by
    apply factor_congr hB
    intro i hi
    rcases hi.lt_or_eq with hlt | rfl
    · rw [update_of_ne hlt.ne, update_of_ne hlt.ne]; exact h i hlt
    · simp only [update_self]
  simp only [kernel, e]

/-- The dependence hypothesis in the form used by `Comparison` (`hKdep`). -/
theorem kernel_dep (hB : DependsLE B) (m : ℕ) (j : Fin n) (x x' : (i : Fin n) → X i)
    (h : ∀ i, i < j → x i = x' i) : kernel B δ m j x = kernel B δ m j x' :=
  funext (kernel_congr hB m j h)

end Kernel

/-! ### The exported criterion -/

/-- Criterion. -/
theorem criterion [∀ j, Nonempty (X j)] (hB : DependsLE B)
    (hδ0 : ∀ ℓ, 0 ≤ δ ℓ) (hδ1 : ∀ ℓ, δ ℓ < 1) (L : Fin n → ℝ)
    (hL : ∀ ℓ : Fin n, ∑ x, P B δ ℓ x * (max 0 (alpha B ℓ x - δ ℓ) / (1 - δ ℓ)) ≤ L ℓ)
    (hsum : ∑ ℓ, L ℓ < 1) :
    ∃ x : (j : Fin n) → X j, ∀ ℓ, x ∉ B ℓ := by
  apply exists_forall_not_mem hB hδ0 hδ1
  calc ∑ ℓ : Fin n, ∑ x ∈ B ℓ, P B δ ((ℓ : ℕ) + 1) x
      = ∑ ℓ : Fin n, ∑ x, P B δ ℓ x * (max 0 (alpha B ℓ x - δ ℓ) / (1 - δ ℓ)) :=
        Finset.sum_congr rfl (fun ℓ _ => sum_mem_P_succ hB (hδ0 ℓ) (hδ1 ℓ))
    _ ≤ ∑ ℓ, L ℓ := Finset.sum_le_sum (fun ℓ _ => hL ℓ)
    _ < 1 := hsum

/-- Criterion, kernel form: the loss integrand may be replaced by any pointwise majorant `h ℓ`,
and `P ℓ` is written as the product of the kernels `kernel B δ ℓ` (the shape of the left-hand
side of the comparison theorem). -/
theorem criterion_kernel [∀ j, Nonempty (X j)] (hB : DependsLE B)
    (hδ0 : ∀ ℓ, 0 ≤ δ ℓ) (hδ1 : ∀ ℓ, δ ℓ < 1) (h : Fin n → ((j : Fin n) → X j) → ℝ)
    (hh : ∀ ℓ x, max 0 (alpha B ℓ x - δ ℓ) / (1 - δ ℓ) ≤ h ℓ x)
    (hsum : ∑ ℓ : Fin n, ∑ x, (∏ j, kernel B δ ℓ j x (x j)) * h ℓ x < 1) :
    ∃ x : (j : Fin n) → X j, ∀ ℓ, x ∉ B ℓ := by
  refine criterion hB hδ0 hδ1 (fun ℓ => ∑ x, (∏ j, kernel B δ ℓ j x (x j)) * h ℓ x)
    (fun ℓ => ?_) hsum
  refine Finset.sum_le_sum (fun x _ => ?_)
  rw [← P_eq_prod_kernel]
  exact mul_le_mul_of_nonneg_left (hh ℓ x) (P_nonneg hδ1 ℓ x)

end MinModulus.Distortion
