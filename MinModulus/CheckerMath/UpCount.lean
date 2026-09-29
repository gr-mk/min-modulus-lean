import MinModulus.CheckerMath.TauLaw

/-!
# `CheckerMath`, part 4: the leaf data of the enumeration (`CheckerImpl.Enum`)

For a leaf `s = s_A(a)` of the enumeration, `CheckerImpl.Enum` uses
* `P(s_A = s) = C[pat]/s` with `C[pat] = Π_q (1 - ν_q/q if a_q = 0, ν_q (q-1)/q if a_q ≥ 1)`
  (`weight_eq_div_smooth`; for an untilted prime, `ν_q = 1`, both factors are `(q-1)/q`);
* `U_p(s) = I/(p^{J-1}(p-1))`, `I = p^{J-1} n_1 + p^{J-2}(σ_1 - σ_2) + σ_2`, where
  `σ_j = #{d ∣ s : d < M_j}`, `M_j = ⌈m/p^j⌉`, `n_1 = τ(s) - σ_1` (`Up_eq_sigma`, stated with the
  uniform scaling `p^2 (p-1)`, valid whenever `m ≤ p^3`, i.e. `J ≤ 3`; for `J = 2` one has
  `σ_2 = 0`, for `J = 1` also `σ_1 = 0`, and the checker's `I/(p^{J-1}(p-1))` is the same real).

`cdiv_le_iff_le_mul` characterizes the thresholds: `⌈m/P⌉ ≤ d ↔ m ≤ d P`.
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth

/-- `⌈m/P⌉ ≤ d ↔ m ≤ d·P` for `P > 0`, with `⌈m/P⌉ = (m + P - 1)/P` (`CheckerImpl.cdiv`). -/
theorem cdiv_le_iff_le_mul {m P d : ℕ} (hP : 0 < P) : (m + P - 1) / P ≤ d ↔ m ≤ d * P := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hP, Nat.succ_mul]
  omega

/-- The three-level weight: for `d ≥ 1`, `m ≤ p^3`, and thresholds `M1`, `M2` with
`M1 ≤ d ↔ m ≤ d p`, `M2 ≤ d ↔ m ≤ d p²`:
`w_p(d) = (p² (1 - [d < M1]) + p ([d < M1] - [d < M2]) + [d < M2]) / (p² (p - 1))`. -/
theorem wp_eq_levels {p m d M1 M2 : ℕ} (hp : 1 < p) (hd : 0 < d) (hm : m ≤ p ^ 3)
    (hM1 : ∀ d, M1 ≤ d ↔ m ≤ d * p) (hM2 : ∀ d, M2 ≤ d ↔ m ≤ d * p ^ 2) :
    wp p m d = ((p : ℝ) ^ 2 * (1 - (if d < M1 then 1 else 0)) +
      (p : ℝ) * ((if d < M1 then 1 else 0) - (if d < M2 then 1 else 0)) +
      (if d < M2 then 1 else 0)) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hdp : d * p ≤ d * p ^ 2 := Nat.mul_le_mul_left d (by nlinarith)
  unfold wp
  by_cases h1 : M1 ≤ d
  · have hm1 : m ≤ d * p := (hM1 d).1 h1
    have h2 : M2 ≤ d := (hM2 d).2 (hm1.trans hdp)
    rw [j0_eq_of hp hd le_rfl (by simpa using hm1) (Or.inl rfl)]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    norm_num
    field_simp
  · by_cases h2 : M2 ≤ d
    · have hm2 : m ≤ d * p ^ 2 := (hM2 d).1 h2
      have hlt : d * p ^ (2 - 1) < m := by
        have := mt (hM1 d).2 h1
        simpa using this
      rw [j0_eq_of hp hd (by norm_num) hm2 (Or.inr hlt)]
      rw [ite_eq_left (by omega), ite_eq_right (by omega)]
      norm_num
      field_simp
    · have hlt : d * p ^ (3 - 1) < m := by
        have := mt (hM2 d).2 h2
        simpa using this
      have hm3 : m ≤ d * p ^ 3 := hm.trans (Nat.le_mul_of_pos_left _ hd)
      have hlt1 : ¬ M1 ≤ d := h1
      rw [j0_eq_of hp hd (by norm_num) hm3 (Or.inr hlt)]
      rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      norm_num
      field_simp

/-- **`U_p(s)` from the small-divisor counts** (`CheckerImpl.Enum`): for `m ≤ p^3`,
thresholds `M1 ≤ d ↔ m ≤ d p`, `M2 ≤ d ↔ m ≤ d p²` (e.g. `M1 = ⌈m/p⌉`, `M2 = ⌈m/p²⌉`, by
`cdiv_le_iff_le_mul`), `σ_j = #{d ∣ s : d < M_j}`:
`U_p(s) = (p² (τ(s) - σ_1) + p (σ_1 - σ_2) + σ_2) / (p² (p - 1))`. -/
theorem Up_eq_sigma {p m s M1 M2 : ℕ} (hp : 1 < p) (hm : m ≤ p ^ 3)
    (hM1 : ∀ d, M1 ≤ d ↔ m ≤ d * p) (hM2 : ∀ d, M2 ≤ d ↔ m ≤ d * p ^ 2) :
    Up p m s = ((p : ℝ) ^ 2 * ((s.divisors.card : ℝ) - ((s.divisors.filter (· < M1)).card : ℝ)) +
      (p : ℝ) * (((s.divisors.filter (· < M1)).card : ℝ) -
        ((s.divisors.filter (· < M2)).card : ℝ)) +
      ((s.divisors.filter (· < M2)).card : ℝ)) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
  unfold Up
  rw [sum_congr rfl fun d hd => wp_eq_levels hp (Nat.pos_of_mem_divisors hd) hm hM1 hM2]
  simp only [div_eq_mul_inv]
  rw [← sum_mul]
  congr 1
  have e1 : ∑ d ∈ s.divisors, (if d < M1 then (1 : ℝ) else 0) =
      ((s.divisors.filter (· < M1)).card : ℝ) := by rw [sum_boole]
  have e2 : ∑ d ∈ s.divisors, (if d < M2 then (1 : ℝ) else 0) =
      ((s.divisors.filter (· < M2)).card : ℝ) := by rw [sum_boole]
  simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
  rw [e1, e2]

/-- **Leaf probability** (`CheckerImpl.Enum`: `P(s_A = s) = C[pat]/s`): below the caps,
`π(a) = (Π_{q ∈ A} (1 - ν_q/q if a_q = 0, ν_q (1 - 1/q) if a_q ≥ 1)) / s(a)`. -/
theorem weight_eq_div_smooth {A : Finset ℕ} {ν : ℕ → ℝ} {γ : ℕ → ℕ} {a : ℕ → ℕ}
    (ha : ∀ q ∈ A, a q < γ q) :
    weight A ν γ a = (∏ q ∈ A, (if a q = 0 then 1 - ν q / q else ν q * (1 - (q : ℝ)⁻¹))) /
      (smooth A a : ℝ) := by
  unfold weight
  have h : ∀ q ∈ A, rho q (ν q) (γ q) (a q) =
      (if a q = 0 then 1 - ν q / q else ν q * (1 - (q : ℝ)⁻¹)) * ((q : ℝ)⁻¹) ^ (a q) := by
    intro q hq
    rw [rho_eq_pointMass (ha q hq)]
    split_ifs with h0
    · simp [h0]
    · ring
  rw [prod_congr rfl h, prod_mul_distrib, div_eq_mul_inv]
  congr 1
  unfold smooth
  push_cast
  rw [← prod_inv_distrib]
  exact prod_congr rfl fun q _ => by rw [inv_pow]

end MinModulus.CheckerMath
