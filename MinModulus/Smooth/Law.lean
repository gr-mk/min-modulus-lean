import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Module 4 (`Smooth`), part 1: the capped tilted exponent law

For a prime `q`, a tilt `ν ∈ [1, q]` and a cap `γ ∈ ℕ`, the random exponent `v = min(V, γ)` where
`P(V ≥ r) = min(1, ν q^{-r})`.  We write `x = q⁻¹`.

* `tailP q ν r = P(V ≥ r)` : `1` for `r = 0`, `ν x^r` for `r ≥ 1`.  For `1 ≤ ν ≤ q` it equals
  `min 1 (ν x^r)` (`tailP_eq_min`), i.e. exactly the `V`-law of the comparison theorem.
* `rho q ν γ a = P(min(V, γ) = a)`:
  - `γ = 0` : `ρ(0) = 1`;
  - `γ ≥ 1` : `ρ(0) = 1 - ν/q`, `ρ(a) = ν x^a (1 - x)` for `1 ≤ a < γ`, `ρ(γ) = ν x^γ`;
  - `ρ(a) = 0` for `a > γ`.
  (`rho_zero_zero`, `rho_zero_of_pos`, `rho_of_pos_of_lt`, `rho_self_of_pos`, `rho_of_gt`.)
* `expect1 q ν γ g = Σ_{a ≤ γ} ρ(a) g(a)`, the one–coordinate expectation.

Main facts: `sum_rho` (normalization, no hypotheses), `rho_nonneg` (`0 ≤ ν ≤ q`),
`expect1_succ` (raising the cap by one adds `P(V ≥ γ+1)·(g(γ+1) - g(γ))`), `expect1_eq_tail`
(Abel/tail formula), `expect1_mono_cap` (monotone coupling in the cap), `expect1_indicator`.
-/

namespace MinModulus.Smooth

open Finset

/-- `tailP q ν r = P(V ≥ r)` for the untruncated tilted law: `1` if `r = 0`, else `ν q^{-r}`. -/
noncomputable def tailP (q : ℕ) (ν : ℝ) (r : ℕ) : ℝ :=
  if r = 0 then 1 else ν * ((q : ℝ)⁻¹) ^ r

/-- The capped tilted exponent law: `rho q ν γ a = P(min(V, γ) = a)`, where
`P(V ≥ r) = tailP q ν r`.  It vanishes for `a > γ`. -/
noncomputable def rho (q : ℕ) (ν : ℝ) (γ a : ℕ) : ℝ :=
  if a < γ then tailP q ν a - tailP q ν (a + 1) else if a = γ then tailP q ν a else 0

/-- One-coordinate expectation `E[g(min(V, γ))] = Σ_{a ≤ γ} ρ(q, ν, γ, a) g(a)`. -/
noncomputable def expect1 (q : ℕ) (ν : ℝ) (γ : ℕ) (g : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (γ + 1), rho q ν γ a * g a

variable {q : ℕ} {ν : ℝ} {γ a r : ℕ}

/-! ### `tailP` -/

@[simp] theorem tailP_zero (q : ℕ) (ν : ℝ) : tailP q ν 0 = 1 := by simp [tailP]

theorem tailP_of_ne_zero (hr : r ≠ 0) : tailP q ν r = ν * ((q : ℝ)⁻¹) ^ r := by
  simp [tailP, hr]

theorem tailP_succ (q : ℕ) (ν : ℝ) (r : ℕ) : tailP q ν (r + 1) = ν * ((q : ℝ)⁻¹) ^ (r + 1) :=
  tailP_of_ne_zero (Nat.succ_ne_zero r)

theorem natCast_inv_le_one (q : ℕ) : ((q : ℝ)⁻¹) ≤ 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hq)

theorem natCast_inv_nonneg (q : ℕ) : 0 ≤ ((q : ℝ)⁻¹) := by positivity

theorem tailP_nonneg (hν : 0 ≤ ν) (q r : ℕ) : 0 ≤ tailP q ν r := by
  unfold tailP
  split_ifs
  · exact zero_le_one
  · exact mul_nonneg hν (pow_nonneg (natCast_inv_nonneg q) r)

/-- `ν q⁻¹ ≤ 1` when `ν ≤ q`. -/
theorem mul_inv_le_one_of_le (hνq : ν ≤ q) : ν * (q : ℝ)⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    rw [← div_eq_mul_inv, div_le_one hq']
    exact hνq

theorem tailP_succ_le (hν : 0 ≤ ν) (hνq : ν ≤ q) (r : ℕ) : tailP q ν (r + 1) ≤ tailP q ν r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa [tailP] using mul_inv_le_one_of_le hνq
  · rw [tailP_succ, tailP_of_ne_zero hr.ne', pow_succ, ← mul_assoc]
    have h1 : 0 ≤ ν * ((q : ℝ)⁻¹) ^ r := mul_nonneg hν (pow_nonneg (natCast_inv_nonneg q) r)
    calc ν * ((q : ℝ)⁻¹) ^ r * (q : ℝ)⁻¹ ≤ ν * ((q : ℝ)⁻¹) ^ r * 1 :=
          mul_le_mul_of_nonneg_left (natCast_inv_le_one q) h1
      _ = ν * ((q : ℝ)⁻¹) ^ r := mul_one _

theorem tailP_antitone (hν : 0 ≤ ν) (hνq : ν ≤ q) : Antitone (tailP q ν) :=
  antitone_nat_of_succ_le (tailP_succ_le hν hνq)

theorem tailP_le_one (hν : 0 ≤ ν) (hνq : ν ≤ q) (r : ℕ) : tailP q ν r ≤ 1 := by
  simpa using tailP_antitone hν hνq (Nat.zero_le r)

/-- For `1 ≤ ν ≤ q`, `tailP q ν r = min 1 (ν q^{-r})`: the tail of the comparison theorem's `V`. -/
theorem tailP_eq_min (h1 : 1 ≤ ν) (hνq : ν ≤ q) (r : ℕ) :
    tailP q ν r = min 1 (ν * ((q : ℝ)⁻¹) ^ r) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [h1]
  · rw [tailP_of_ne_zero hr.ne', eq_comm, min_eq_right]
    have := tailP_le_one (by linarith) hνq r
    rwa [tailP_of_ne_zero hr.ne'] at this

/-! ### `rho` -/

theorem rho_of_lt (h : a < γ) : rho q ν γ a = tailP q ν a - tailP q ν (a + 1) := by
  simp [rho, h]

@[simp] theorem rho_self (q : ℕ) (ν : ℝ) (γ : ℕ) : rho q ν γ γ = tailP q ν γ := by
  simp [rho]

theorem rho_of_gt (h : γ < a) : rho q ν γ a = 0 := by
  have h1 : ¬ a < γ := by omega
  have h2 : a ≠ γ := by omega
  simp [rho, h1, h2]

@[simp] theorem rho_zero_zero (q : ℕ) (ν : ℝ) : rho q ν 0 0 = 1 := by simp

theorem rho_zero_of_pos (h : 0 < γ) : rho q ν γ 0 = 1 - ν / q := by
  rw [rho_of_lt h, tailP_zero, tailP_succ]
  simp [div_eq_mul_inv]

theorem rho_of_pos_of_lt (ha : 0 < a) (h : a < γ) :
    rho q ν γ a = ν * ((q : ℝ)⁻¹) ^ a * (1 - (q : ℝ)⁻¹) := by
  rw [rho_of_lt h, tailP_of_ne_zero ha.ne', tailP_succ, pow_succ]
  ring

theorem rho_self_of_pos (h : 0 < γ) : rho q ν γ γ = ν * ((q : ℝ)⁻¹) ^ γ := by
  rw [rho_self, tailP_of_ne_zero h.ne']

/-- The law agrees below the cap: `ρ(q,ν,γ,a) = P(V = a)` for `a < γ`, independently of `γ`. -/
theorem rho_eq_of_lt_of_lt {γ' : ℕ} (h : a < γ) (h' : a < γ') : rho q ν γ a = rho q ν γ' a := by
  rw [rho_of_lt h, rho_of_lt h']

/-- The `V`-law form (comparison theorem): for `1 ≤ ν ≤ q`,
`ρ(a) = min(1, ν q^{-a}) - min(1, ν q^{-(a+1)})` for `a < γ`. -/
theorem rho_eq_min_sub (h1 : 1 ≤ ν) (hνq : ν ≤ q) (h : a < γ) :
    rho q ν γ a = min 1 (ν * ((q : ℝ)⁻¹) ^ a) - min 1 (ν * ((q : ℝ)⁻¹) ^ (a + 1)) := by
  rw [rho_of_lt h, tailP_eq_min h1 hνq, tailP_eq_min h1 hνq]

/-- The `V`-law form at the cap: `ρ(γ) = min(1, ν q^{-γ})` for `1 ≤ ν ≤ q`. -/
theorem rho_self_eq_min (h1 : 1 ≤ ν) (hνq : ν ≤ q) (γ : ℕ) :
    rho q ν γ γ = min 1 (ν * ((q : ℝ)⁻¹) ^ γ) := by
  rw [rho_self, tailP_eq_min h1 hνq]

theorem rho_nonneg (hν : 0 ≤ ν) (hνq : ν ≤ q) (γ a : ℕ) : 0 ≤ rho q ν γ a := by
  unfold rho
  split_ifs
  · exact sub_nonneg.2 (tailP_succ_le hν hνq a)
  · exact tailP_nonneg hν q a
  · exact le_rfl

/-! ### One-coordinate expectations -/

@[simp] theorem expect1_zero_cap (q : ℕ) (ν : ℝ) (g : ℕ → ℝ) : expect1 q ν 0 g = g 0 := by
  simp [expect1]

/-- Raising the cap from `γ` to `γ + 1` adds `P(V ≥ γ+1) · (g(γ+1) - g(γ))`. -/
theorem expect1_succ (q : ℕ) (ν : ℝ) (γ : ℕ) (g : ℕ → ℝ) :
    expect1 q ν (γ + 1) g = expect1 q ν γ g + tailP q ν (γ + 1) * (g (γ + 1) - g γ) := by
  simp only [expect1]
  rw [sum_range_succ, sum_range_succ, sum_range_succ]
  have h1 : ∑ x ∈ range γ, rho q ν (γ + 1) x * g x = ∑ x ∈ range γ, rho q ν γ x * g x := by
    refine sum_congr rfl fun a ha => ?_
    have ha' := mem_range.1 ha
    rw [rho_of_lt (by omega : a < γ + 1), rho_of_lt ha']
  rw [h1, rho_of_lt (Nat.lt_succ_self γ), rho_self, rho_self]
  ring

/-- Tail (Abel) formula: `E_γ[g] = g 0 + Σ_{r<γ} P(V ≥ r+1) (g(r+1) - g(r))`. -/
theorem expect1_eq_tail (q : ℕ) (ν : ℝ) (γ : ℕ) (g : ℕ → ℝ) :
    expect1 q ν γ g = g 0 + ∑ r ∈ range γ, tailP q ν (r + 1) * (g (r + 1) - g r) := by
  induction γ with
  | zero => simp
  | succ γ ih => rw [expect1_succ, ih, sum_range_succ, add_assoc]

/-- (i), one coordinate: normalization (no hypotheses needed). -/
theorem sum_rho (q : ℕ) (ν : ℝ) (γ : ℕ) : ∑ a ∈ range (γ + 1), rho q ν γ a = 1 := by
  have h := expect1_eq_tail q ν γ (fun _ => 1)
  simpa [expect1] using h

theorem expect1_const (q : ℕ) (ν : ℝ) (γ : ℕ) (c : ℝ) : expect1 q ν γ (fun _ => c) = c := by
  simp [expect1, ← sum_mul, sum_rho]

theorem expect1_add (q : ℕ) (ν : ℝ) (γ : ℕ) (f g : ℕ → ℝ) :
    expect1 q ν γ (fun a => f a + g a) = expect1 q ν γ f + expect1 q ν γ g := by
  simp [expect1, mul_add, sum_add_distrib]

theorem expect1_const_mul (q : ℕ) (ν : ℝ) (γ : ℕ) (c : ℝ) (g : ℕ → ℝ) :
    expect1 q ν γ (fun a => c * g a) = c * expect1 q ν γ g := by
  simp [expect1, mul_sum, mul_left_comm]

theorem expect1_mono (hν : 0 ≤ ν) (hνq : ν ≤ q) {f g : ℕ → ℝ} (h : ∀ a ≤ γ, f a ≤ g a) :
    expect1 q ν γ f ≤ expect1 q ν γ g := by
  refine sum_le_sum fun a ha => ?_
  exact mul_le_mul_of_nonneg_left (h a (Nat.lt_succ_iff.1 (mem_range.1 ha)))
    (rho_nonneg hν hνq γ a)

theorem expect1_nonneg (hν : 0 ≤ ν) (hνq : ν ≤ q) {g : ℕ → ℝ} (h : ∀ a ≤ γ, 0 ≤ g a) :
    0 ≤ expect1 q ν γ g := by
  simpa [expect1_const] using expect1_mono (q := q) (γ := γ) hν hνq (f := fun _ => 0) h

/-- (ii), one coordinate: monotone coupling in the cap.  Only `0 ≤ ν` is needed. -/
theorem expect1_mono_cap (hν : 0 ≤ ν) {g : ℕ → ℝ} (hg : Monotone g) {γ γ' : ℕ} (h : γ ≤ γ') :
    expect1 q ν γ g ≤ expect1 q ν γ' g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [← add_assoc, expect1_succ]
    have := mul_nonneg (tailP_nonneg hν q (γ + k + 1)) (sub_nonneg.2 (hg (Nat.le_succ (γ + k))))
    linarith [ih (Nat.le_add_right γ k)]

/-- One coordinate: for nondecreasing `g`, `E_γ[g]` is nondecreasing in the tilt `ν`
(no sign condition needed). -/
theorem expect1_mono_tilt {ν ν' : ℝ} (h : ν ≤ ν') {g : ℕ → ℝ} (hg : Monotone g) (q γ : ℕ) :
    expect1 q ν γ g ≤ expect1 q ν' γ g := by
  rw [expect1_eq_tail, expect1_eq_tail]
  have : ∀ r ∈ range γ, tailP q ν (r + 1) * (g (r + 1) - g r) ≤
      tailP q ν' (r + 1) * (g (r + 1) - g r) := by
    intro r _
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.2 (hg (Nat.le_succ r)))
    rw [tailP_succ, tailP_succ]
    exact mul_le_mul_of_nonneg_right h (pow_nonneg (natCast_inv_nonneg q) _)
  linarith [sum_le_sum this]

/-- **Exact coupling**, one coordinate: for `γ ≤ γ'` the law with cap `γ` is the image of the law
with cap `γ'` under `a ↦ min a γ`. -/
theorem expect1_clip {γ γ' : ℕ} (h : γ ≤ γ') (G : ℕ → ℝ) :
    expect1 q ν γ G = expect1 q ν γ' (fun a => G (min a γ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
    refine sum_congr rfl fun a ha => ?_
    have : a ≤ γ := Nat.lt_succ_iff.1 (mem_range.1 ha)
    simp [min_eq_left this]
  | succ k ih =>
    rw [← add_assoc, expect1_succ, ← ih (Nat.le_add_right γ k)]
    have h1 : min (γ + k + 1) γ = γ := min_eq_right (by omega)
    simp [h1]

/-- `P(min(V, γ) ≥ r) = P(V ≥ r)` for `r ≤ γ`. -/
theorem expect1_indicator (hr : r ≤ γ) :
    expect1 q ν γ (fun a => if r ≤ a then 1 else 0) = tailP q ν r := by
  rw [expect1_eq_tail]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp
  · have h0 : ¬ r ≤ 0 := by omega
    simp only [h0, ↓reduceIte, zero_add]
    rw [sum_eq_single (r - 1)]
    · have h1 : r - 1 + 1 = r := by omega
      have h2 : ¬ r ≤ r - 1 := by omega
      simp [h1, h2]
    · intro b _ hb
      by_cases h3 : r ≤ b
      · have h4 : r ≤ b + 1 := by omega
        simp [h3, h4]
      · have h4 : ¬ r ≤ b + 1 := by omega
        simp [h3, h4]
    · intro h
      exfalso
      exact h (mem_range.2 (by omega))

theorem expect1_indicator_of_lt (hr : γ < r) :
    expect1 q ν γ (fun a => if r ≤ a then 1 else 0) = 0 := by
  refine sum_eq_zero fun a ha => ?_
  have : ¬ r ≤ a := by have := mem_range.1 ha; omega
  simp [this]

end MinModulus.Smooth
