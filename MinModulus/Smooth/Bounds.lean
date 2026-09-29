import MinModulus.Smooth.Weights
import MinModulus.Smooth.Hinge
import MinModulus.Smooth.Moments

/-!
# Module 4 (`Smooth`), part 7: assembled bounds for the loss at one prime

* `hinge_Up_le_tau` : pointwise `(U_p(s) - t)^+ ≤ c_θ(t)/(p-1)^θ · τ(s)^θ`;
* `expect_hinge_Up_le` : `E_γ[(U_p(s) - t)^+] ≤ c_θ(t)/(p-1)^θ · Π_{q ∈ Ps} E_q[(v_q+1)^θ]`;
* `expect_hinge_Up_le_prod` : the same with per-prime upper bounds `B q`
  (to be combined with `expect1_rpow_le`, uniform in `γ`);
* `expect_hinge_Up_le_two` : closed form for `θ = 2`:
  `E_γ[(U_p(s) - t)^+] ≤ (1/(4t))/(p-1)² · Π_{q ∈ Ps} (1 + ν_q(3q-1)/(q-1)²)`, every `γ`;
* `expect_hinge_le_sq_div` : `E[(F - t)^+] ≤ E[F²]/(4t)` (BBMST second moment);
* first moment: `Up_smooth_eq` (`U_p(s(v)) = Σ_{b ∈ box Ps v} w_p(s(b))`) and the exact formula
  `expect_Up_eq : E_γ[U_p(s)] = Σ_{b ∈ box Ps γ} w_p(s(b)) · Π_{q ∈ Ps} P(V_q ≥ b q)`.
-/

namespace MinModulus.Smooth

open Finset

variable {Ps : Finset ℕ} {ν : ℕ → ℝ} {p : ℕ} {t θ : ℝ}

/-! ### `θ = 5/2`: a fully rational certificate for the per-prime moment -/

/-- **θ = 5/2, rational certificate, uniform in the cap.**  Let `x = q⁻¹`.  If `0 ≤ r < 1` with
`(K+3)^5 ≤ (r q)² (K+2)^5` (i.e. `((K+3)/(K+2))^{5/2} x ≤ r`), `c a ≥ 0` with `(a+2)^5 ≤ (c a)²`
for `a ≤ K` (i.e. `c a ≥ (a+2)^{5/2}`), and
`B ≥ Σ_{a<K} x^{a+1}(c a - 1) + x^{K+1} c K / (1 - r)`, then `E_γ[(v+1)^{5/2}] ≤ 1 + ν(1 - x) B`
for every cap `γ`. -/
theorem expect1_five_halves_le {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) (K : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hr : ((K : ℝ) + 3) ^ 5 ≤ (r * q) ^ 2 * ((K : ℝ) + 2) ^ 5)
    (c : ℕ → ℝ) (hc0 : ∀ a, a ≤ K → 0 ≤ c a) (hc : ∀ a, a ≤ K → ((a : ℝ) + 2) ^ 5 ≤ c a ^ 2)
    {B : ℝ} (hB : ∑ a ∈ range K, ((q : ℝ)⁻¹) ^ (a + 1) * (c a - 1) +
      ((q : ℝ)⁻¹) ^ (K + 1) * c K / (1 - r) ≤ B) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤ 1 + ν * (1 - (q : ℝ)⁻¹) * B := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hx0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have h1r : 0 < 1 - r := by linarith
  have hratio : (((K : ℝ) + 3) / ((K : ℝ) + 2)) ^ (5 / 2 : ℝ) * (q : ℝ)⁻¹ ≤ r := by
    have hK2 : (0 : ℝ) < (K : ℝ) + 2 := by positivity
    have hy : 0 ≤ ((K : ℝ) + 3) / ((K : ℝ) + 2) := by positivity
    have hrq : 0 ≤ r * q := by positivity
    have h5 : (((K : ℝ) + 3) / ((K : ℝ) + 2)) ^ (5 / 2 : ℝ) ≤ r * q := by
      rw [rpow_five_halves_le_iff hy hrq, div_pow, div_le_iff₀ (by positivity)]
      exact hr
    calc (((K : ℝ) + 3) / ((K : ℝ) + 2)) ^ (5 / 2 : ℝ) * (q : ℝ)⁻¹
        ≤ r * q * (q : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h5 hx0
      _ = r := by field_simp
  refine expect1_rpow_le hq hν (by norm_num) K hratio hr1 (le_trans ?_ hB) γ
  have hcb : ∀ a, a ≤ K → ((a : ℝ) + 2) ^ (5 / 2 : ℝ) ≤ c a := fun a ha =>
    (rpow_five_halves_le_iff (by positivity) (hc0 a ha)).2 (hc a ha)
  have hsum : ∑ a ∈ range K, ((q : ℝ)⁻¹) ^ (a + 1) * (((a : ℝ) + 2) ^ (5 / 2 : ℝ) - 1) ≤
      ∑ a ∈ range K, ((q : ℝ)⁻¹) ^ (a + 1) * (c a - 1) :=
    sum_le_sum fun a ha => mul_le_mul_of_nonneg_left
      (by linarith [hcb a (le_of_lt (mem_range.1 ha))]) (pow_nonneg hx0 _)
  have htail : ((q : ℝ)⁻¹) ^ (K + 1) * ((K : ℝ) + 2) ^ (5 / 2 : ℝ) / (1 - r) ≤
      ((q : ℝ)⁻¹) ^ (K + 1) * c K / (1 - r) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hcb K le_rfl) (pow_nonneg hx0 _))
      h1r.le
  linarith

/-! ### Pointwise chain -/

/-- `(U_p(s) - t)^+ ≤ c_θ(t)/(p-1)^θ · τ(s)^θ` for `p > 1`, `t > 0`, `θ > 1`. -/
theorem hinge_Up_le_tau (hp : 1 < p) (m s : ℕ) (ht : 0 < t) (hθ : 1 < θ) :
    max 0 (Up p m s - t) ≤ ctheta θ t / ((p : ℝ) - 1) ^ θ * (s.divisors.card : ℝ) ^ θ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  calc max 0 (Up p m s - t) ≤ ctheta θ t * (Up p m s) ^ θ :=
        hinge_le_ctheta_mul_rpow ht hθ (Up_nonneg hp m s)
    _ ≤ ctheta θ t * ((s.divisors.card : ℝ) / ((p : ℝ) - 1)) ^ θ :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Up_nonneg hp m s) (Up_le_card_div hp m s) (by linarith))
          (ctheta_pos ht hθ).le
    _ = ctheta θ t / ((p : ℝ) - 1) ^ θ * (s.divisors.card : ℝ) ^ θ := by
        rw [Real.div_rpow (by positivity) hp0.le]
        ring

/-- The hinge integrand `v ↦ (U_p(s(v)) - t)^+` is monotone, so `expect_mono_cap`,
`expect_mono_tilt`, `expect_le_of_subset` and `expect_le_of_forall_ge_cap` apply to it. -/
theorem monotone_hinge_Up (hPs : ∀ q ∈ Ps, 0 < q) (hp : 1 < p) (m : ℕ) (t : ℝ) :
    Monotone (fun v => max 0 (Up p m (smooth Ps v) - t)) :=
  fun _ _ h => max_le_max le_rfl (sub_le_sub_right (monotone_Up_smooth hp m hPs h) t)

/-! ### Expectation chains -/

/-- **θ-moment bound** for the loss at `p`:
`E_γ[(U_p(s) - t)^+] ≤ c_θ(t)/(p-1)^θ · Π_{q ∈ Ps} E_q[(v_q + 1)^θ]`. -/
theorem expect_hinge_Up_le (hPs : ∀ q ∈ Ps, q.Prime) (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (hp : 1 < p) (m : ℕ) (ht : 0 < t) (hθ : 1 < θ) :
    expect Ps ν γ (fun v => max 0 (Up p m (smooth Ps v) - t)) ≤
      ctheta θ t / ((p : ℝ) - 1) ^ θ *
        ∏ q ∈ Ps, expect1 q (ν q) (γ q) (fun a => ((a : ℝ) + 1) ^ θ) := by
  rw [← expect_tau_rpow hPs, ← expect_const_mul]
  exact expect_mono hν fun v _ => hinge_Up_le_tau hp m _ ht hθ

/-- The θ-moment bound with per-prime bounds `B q ≥ E_q[(v_q + 1)^θ]` (e.g. `expect1_rpow_le`). -/
theorem expect_hinge_Up_le_prod (hPs : ∀ q ∈ Ps, q.Prime) (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (hp : 1 < p) (m : ℕ) (ht : 0 < t) (hθ : 1 < θ) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Ps, expect1 q (ν q) (γ q) (fun a => ((a : ℝ) + 1) ^ θ) ≤ B q) :
    expect Ps ν γ (fun v => max 0 (Up p m (smooth Ps v) - t)) ≤
      ctheta θ t / ((p : ℝ) - 1) ^ θ * ∏ q ∈ Ps, B q := by
  refine (expect_hinge_Up_le hPs hν γ hp m ht hθ).trans ?_
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hc : 0 ≤ ctheta θ t / ((p : ℝ) - 1) ^ θ :=
    div_nonneg (ctheta_pos ht hθ).le (Real.rpow_nonneg (by linarith) _)
  refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun q hq => ?_) hB) hc
  exact expect1_nonneg (hν q hq).1 (hν q hq).2 fun a _ => Real.rpow_nonneg (by positivity) θ

/-- **θ = 2 in closed form**, uniform in the caps:
`E_γ[(U_p(s) - t)^+] ≤ (1/(4t))/(p-1)² · Π_{q ∈ Ps} (1 + ν_q (3q-1)/(q-1)²)`. -/
theorem expect_hinge_Up_le_two (hPs : ∀ q ∈ Ps, q.Prime) (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (hp : 1 < p) (m : ℕ) (ht : 0 < t) :
    expect Ps ν γ (fun v => max 0 (Up p m (smooth Ps v) - t)) ≤
      1 / (4 * t) / ((p : ℝ) - 1) ^ 2 *
        ∏ q ∈ Ps, (1 + ν q * (3 * q - 1) / ((q : ℝ) - 1) ^ 2) := by
  have h := expect_hinge_Up_le_prod hPs hν γ hp m ht (by norm_num : (1 : ℝ) < 2)
    (fun q => 1 + ν q * (3 * q - 1) / ((q : ℝ) - 1) ^ 2)
    (fun q hq => expect1_rpow_two_le (hPs q hq).one_lt (hν q hq).1 (γ q))
  rwa [ctheta_two ht, Real.rpow_two] at h

/-- BBMST's second-moment bound, in expectation: `E[(F - t)^+] ≤ E[F²]/(4t)`. -/
theorem expect_hinge_le_sq_div (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (ht : 0 < t)
    (F : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ (fun v => max 0 (F v - t)) ≤ expect Ps ν γ (fun v => F v ^ 2) / (4 * t) := by
  rw [div_eq_mul_inv, ← expect_mul_const]
  refine expect_mono hν fun v _ => ?_
  rw [← div_eq_mul_inv]
  exact hinge_le_sq_div ht (F v)

/-- First moment: `(U - t)^+ ≤ U` for `t ≥ 0`, `U ≥ 0`. -/
theorem hinge_le_self (ht : 0 ≤ t) {u : ℝ} (hu : 0 ≤ u) : max 0 (u - t) ≤ u :=
  max_le hu (by linarith)

/-! ### The checker's splitting `s = s_A · s_B` -/

/-- For configurations `v` on `A` and `w` on `B` (disjoint sets of primes),
`U_p(s_{A∪B}(v + w)) ≤ U_p(s_A(v)) + (τ(s_B(w)) - 1) τ(s_A(v))/(p - 1)`. -/
theorem Up_smooth_union_le {A B : Finset ℕ} (hAB : Disjoint A B) (hA : ∀ q ∈ A, q.Prime)
    (hB : ∀ q ∈ B, q.Prime) (hp : 1 < p) (m : ℕ) {v w : ℕ → ℕ} (hv : ∀ q ∈ B, v q = 0)
    (hw : ∀ q ∈ A, w q = 0) :
    Up p m (smooth (A ∪ B) (v + w)) ≤ Up p m (smooth A v) +
      (((smooth B w).divisors.card : ℝ) - 1) * ((smooth A v).divisors.card : ℝ) /
        ((p : ℝ) - 1) := by
  rw [smooth_union_add hAB hv hw]
  exact Up_mul_le hp m (coprime_smooth_of_disjoint hAB hA hB v w)
    (smooth_ne_zero (fun q hq => (hA q hq).pos) v) (smooth_ne_zero (fun q hq => (hB q hq).pos) w)

/-! ### A closed-form fallback for `θ = 5/2` -/

/-- `y^{5/2} ≤ (y² + y³)/2` for `y ≥ 0` (AM–GM). -/
theorem rpow_five_halves_le_avg {y : ℝ} (hy : 0 ≤ y) : y ^ (5 / 2 : ℝ) ≤ (y ^ 2 + y ^ 3) / 2 := by
  rw [rpow_five_halves_le_iff hy (by positivity)]
  nlinarith [sq_nonneg (y ^ 2 - y ^ 3), pow_nonneg hy 4, pow_nonneg hy 5]

/-- **θ = 5/2, closed form, uniform in the cap** (cruder than `expect1_five_halves_le`):
`E_γ[(v+1)^{5/2}] ≤ 1 + ν ((3q-1)/(q-1)² + (7q²-2q+1)/(q-1)³)/2`. -/
theorem expect1_five_halves_le_closed {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) (hνq : ν ≤ q)
    (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤
      1 + ν * ((3 * q - 1) / ((q : ℝ) - 1) ^ 2 +
        (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3) / 2 := by
  have h1 : expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤
      expect1 q ν γ (fun a => (1 / 2 : ℝ) * (((a : ℝ) + 1) ^ 2 + ((a : ℝ) + 1) ^ 3)) :=
    expect1_mono hν hνq fun a _ => by
      have := rpow_five_halves_le_avg (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1)
      linarith
  rw [expect1_const_mul, expect1_add] at h1
  have h2 := expect1_sq_le hq hν γ
  have h3 := expect1_cube_le hq hν γ
  have e : 1 + ν * ((3 * q - 1) / ((q : ℝ) - 1) ^ 2 +
      (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3) / 2 =
      (1 / 2 : ℝ) * ((1 + ν * (3 * q - 1) / ((q : ℝ) - 1) ^ 2) +
        (1 + ν * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3)) := by ring
  rw [e]
  linarith

/-! ### The first moment `E[U_p(s)]` -/

/-- `U_p(s(v)) = Σ_{b ∈ box Ps v} w_p(s(b))` (divisors of `s(v)` are the `s(b)`, `b ≤ v`). -/
theorem Up_smooth_eq (hPs : ∀ q ∈ Ps, q.Prime) (p m : ℕ) (v : ℕ → ℕ) :
    Up p m (smooth Ps v) = ∑ b ∈ box Ps v, wp p m (smooth Ps b) := by
  unfold Up
  rw [divisors_smooth hPs, sum_image (smooth_injOn_box hPs v)]

theorem box_eq_filter {γ v : ℕ → ℕ} (hv : ∀ q ∈ Ps, v q ≤ γ q) :
    box Ps v = (box Ps γ).filter (fun b => ∀ q ∈ Ps, b q ≤ v q) := by
  ext b
  simp only [mem_filter, mem_box]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun q hq => (h1 q hq).trans (hv q hq), h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩

/-- **Exact first moment**: `E_γ[U_p(s)] = Σ_{b ∈ box Ps γ} w_p(s(b)) · Π_{q ∈ Ps} P(V_q ≥ b q)`. -/
theorem expect_Up_eq (hPs : ∀ q ∈ Ps, q.Prime) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (p m : ℕ) :
    expect Ps ν γ (fun v => Up p m (smooth Ps v)) =
      ∑ b ∈ box Ps γ, wp p m (smooth Ps b) * ∏ q ∈ Ps, tailP q (ν q) (b q) := by
  have h1 : ∀ v ∈ box Ps γ, Up p m (smooth Ps v) = ∑ b ∈ box Ps γ,
      wp p m (smooth Ps b) * ∏ q ∈ Ps, (if b q ≤ v q then (1 : ℝ) else 0) := by
    intro v hv
    rw [Up_smooth_eq hPs, box_eq_filter (mem_box.1 hv).1, sum_filter]
    refine sum_congr rfl fun b _ => ?_
    rw [prod_boole]
    split_ifs <;> simp
  rw [expect_congr_fun h1, expect_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [expect_const_mul, expect_prod Ps ν γ (fun q a => if b q ≤ a then (1 : ℝ) else 0)]
  congr 1
  exact prod_congr rfl fun q hq => expect1_indicator ((mem_box.1 hb).1 q hq)

end MinModulus.Smooth
