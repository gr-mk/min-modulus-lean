import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Module 4 (`Smooth`), part 5: pointwise hinge inequalities, half-integer powers

* `ctheta θ t = (t/(θ-1)) · (θ t/(θ-1))^{-θ}`, the least constant with `(u - t)^+ ≤ c u^θ` (`u ≥ 0`).
* (v) `hinge_le_ctheta_mul_rpow` : `max 0 (u - t) ≤ ctheta θ t * u^θ` for `t > 0`, `θ > 1`, `u ≥ 0`;
  `hinge_le_sq_div` : `max 0 (u - t) ≤ u²/(4t)` for `t > 0` (all real `u`).
* Closed forms `ctheta_two : ctheta 2 t = 1/(4t)`, `ctheta_three : ctheta 3 t = 4/(27 t²)`;
  rational certificates `ctheta_le_iff`, `ctheta_five_halves_le`.
* Half-integer powers: `rpow_half_nat_le_iff : y^(n/2) ≤ c ↔ y^n ≤ c²` (for `y, c ≥ 0`),
  `le_rpow_half_nat_iff`, and `rpow_five_halves : y^(5/2) = y² · √y`.
-/

namespace MinModulus.Smooth

/-- `c_θ(t) = (t/(θ-1)) · (θ t/(θ-1))^{-θ}`. -/
noncomputable def ctheta (θ t : ℝ) : ℝ :=
  t / (θ - 1) * (θ * t / (θ - 1)) ^ (-θ)

variable {θ t u : ℝ}

theorem ctheta_pos (ht : 0 < t) (hθ : 1 < θ) : 0 < ctheta θ t := by
  unfold ctheta
  have h1 : 0 < θ - 1 := by linarith
  have h2 : 0 < θ * t / (θ - 1) := div_pos (mul_pos (by linarith) ht) h1
  exact mul_pos (div_pos ht h1) (Real.rpow_pos_of_pos h2 _)

/-- (v) `(u - t)^+ ≤ c_θ(t) u^θ` for `t > 0`, `θ > 1`, `u ≥ 0`. -/
theorem hinge_le_ctheta_mul_rpow (ht : 0 < t) (hθ : 1 < θ) (hu : 0 ≤ u) :
    max 0 (u - t) ≤ ctheta θ t * u ^ θ := by
  rcases le_or_gt u t with hut | hut
  · rw [max_eq_left (by linarith)]
    exact mul_nonneg (ctheta_pos ht hθ).le (Real.rpow_nonneg hu θ)
  · rw [max_eq_right (by linarith)]
    have h1 : 0 < θ - 1 := by linarith
    have hus : 0 < θ * t / (θ - 1) := div_pos (mul_pos (by linarith) ht) h1
    set us := θ * t / (θ - 1) with hus_def
    have hs : -1 ≤ u / us - 1 := by
      have : 0 ≤ u / us := div_nonneg hu hus.le
      linarith
    have hb := one_add_mul_self_le_rpow_one_add hs hθ.le
    rw [show (1 : ℝ) + (u / us - 1) = u / us by ring] at hb
    have hc : ctheta θ t * u ^ θ = t / (θ - 1) * (u / us) ^ θ := by
      unfold ctheta
      rw [Real.div_rpow hu hus.le, Real.rpow_neg hus.le]
      ring
    rw [hc]
    have hθ0 : θ ≠ 0 := by linarith
    have ht0 : t ≠ 0 := ht.ne'
    have h10 : θ - 1 ≠ 0 := h1.ne'
    calc u - t = t / (θ - 1) * (1 + θ * (u / us - 1)) := by
          rw [hus_def]
          field_simp
          ring
      _ ≤ t / (θ - 1) * (u / us) ^ θ := mul_le_mul_of_nonneg_left hb (div_pos ht h1).le

/-- (v) `(u - t)^+ ≤ u²/(4t)` for `t > 0`. -/
theorem hinge_le_sq_div (ht : 0 < t) (u : ℝ) : max 0 (u - t) ≤ u ^ 2 / (4 * t) := by
  apply max_le
  · positivity
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (u - 2 * t)]

theorem ctheta_two (ht : 0 < t) : ctheta 2 t = 1 / (4 * t) := by
  unfold ctheta
  rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num; positivity),
    Real.rpow_natCast]
  field_simp
  ring

theorem ctheta_three (ht : 0 < t) : ctheta 3 t = 4 / (27 * t ^ 2) := by
  unfold ctheta
  rw [show (-(3 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num; positivity),
    Real.rpow_natCast]
  field_simp
  ring

/-- Certificate form: `c_θ(t) ≤ C ↔ t/(θ-1) ≤ C · (θ t/(θ-1))^θ`. -/
theorem ctheta_le_iff (ht : 0 < t) (hθ : 1 < θ) (C : ℝ) :
    ctheta θ t ≤ C ↔ t / (θ - 1) ≤ C * (θ * t / (θ - 1)) ^ θ := by
  have h1 : 0 < θ - 1 := by linarith
  have hus : 0 < θ * t / (θ - 1) := div_pos (mul_pos (by linarith) ht) h1
  have hpow : 0 < (θ * t / (θ - 1)) ^ θ := Real.rpow_pos_of_pos hus θ
  unfold ctheta
  rw [Real.rpow_neg hus.le, ← div_eq_mul_inv, div_le_iff₀ hpow]

/-! ### Half-integer powers -/

theorem rpow_half_nat_sq {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : (y ^ ((n : ℝ) / 2)) ^ 2 = y ^ n := by
  rw [← Real.rpow_natCast (y ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul hy]
  norm_num

/-- `y^{n/2} ≤ c ↔ y^n ≤ c²` for `y, c ≥ 0`: upper bounds of half-integer powers are
certified by a rational inequality. -/
theorem rpow_half_nat_le_iff {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (n : ℕ) :
    y ^ ((n : ℝ) / 2) ≤ c ↔ y ^ n ≤ c ^ 2 := by
  rw [← rpow_half_nat_sq hy n]
  exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hy _) hc two_ne_zero).symm

/-- `c ≤ y^{n/2} ↔ c² ≤ y^n` for `y, c ≥ 0` (lower bounds). -/
theorem le_rpow_half_nat_iff {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (n : ℕ) :
    c ≤ y ^ ((n : ℝ) / 2) ↔ c ^ 2 ≤ y ^ n := by
  rw [← rpow_half_nat_sq hy n]
  exact (pow_le_pow_iff_left₀ hc (Real.rpow_nonneg hy _) two_ne_zero).symm

theorem five_halves_eq : (5 / 2 : ℝ) = ((5 : ℕ) : ℝ) / 2 := by norm_num

theorem rpow_five_halves_le_iff {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) :
    y ^ (5 / 2 : ℝ) ≤ c ↔ y ^ 5 ≤ c ^ 2 := by
  rw [five_halves_eq]
  exact rpow_half_nat_le_iff hy hc 5

theorem le_rpow_five_halves_iff {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) :
    c ≤ y ^ (5 / 2 : ℝ) ↔ c ^ 2 ≤ y ^ 5 := by
  rw [five_halves_eq]
  exact le_rpow_half_nat_iff hy hc 5

/-- `y^{5/2} = y² · √y` for `y ≥ 0`. -/
theorem rpow_five_halves {y : ℝ} (hy : 0 ≤ y) : y ^ (5 / 2 : ℝ) = y ^ 2 * Real.sqrt y := by
  rw [Real.sqrt_eq_rpow, show (5 / 2 : ℝ) = (2 : ℕ) + 1 / 2 by norm_num,
    Real.rpow_add' hy (by norm_num), Real.rpow_natCast]

/-- Rational certificate for `c_{5/2}(t) = (2t/3)(5t/3)^{-5/2}`: if `C ≥ 0` and
`(2t/3)² ≤ C² (5t/3)⁵` then `c_{5/2}(t) ≤ C`. -/
theorem ctheta_five_halves_le (ht : 0 < t) {C : ℝ} (hC : 0 ≤ C)
    (h : (2 * t / 3) ^ 2 ≤ C ^ 2 * (5 * t / 3) ^ 5) : ctheta (5 / 2) t ≤ C := by
  rw [ctheta_le_iff ht (by norm_num)]
  have e1 : t / ((5 / 2 : ℝ) - 1) = 2 * t / 3 := by ring
  have e2 : (5 / 2 : ℝ) * t / ((5 / 2 : ℝ) - 1) = 5 * t / 3 := by ring
  rw [e1, e2]
  have hy : 0 ≤ 5 * t / 3 := by positivity
  have hX := rpow_half_nat_sq hy 5
  rw [← five_halves_eq] at hX
  have hlhs : 0 ≤ 2 * t / 3 := by positivity
  have hrhs : 0 ≤ C * (5 * t / 3) ^ (5 / 2 : ℝ) := mul_nonneg hC (Real.rpow_nonneg hy _)
  rw [← pow_le_pow_iff_left₀ hlhs hrhs two_ne_zero, mul_pow, hX]
  exact h

end MinModulus.Smooth
