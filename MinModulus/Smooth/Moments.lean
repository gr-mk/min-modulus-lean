import MinModulus.Smooth.Law
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Module 4 (`Smooth`), part 6: uniform-in-the-cap moment bounds `E_γ[(v+1)^θ]`

Throughout `x = q⁻¹` and `q > 1`.

**Exact formulas and idealized closed forms** (`θ = 2, 3`):
* `expect1_sq_eq`   : `E_γ[(v+1)²] = 1 + ν (x(3-x) - x^{γ+1}(2 + (2γ+1)(1-x)))/(1-x)²`;
* `expect1_sq_le`   : `E_γ[(v+1)²] ≤ 1 + ν(3q-1)/(q-1)²` for every cap `γ`;
* `tendsto_expect1_sq` : `E_γ[(v+1)²] → 1 + ν(3q-1)/(q-1)²` as `γ → ∞` (so the bound is sharp);
* `expect1_cube_eq`, `expect1_cube_le`, `tendsto_expect1_cube` : the same for `θ = 3` with idealized
  value `1 + ν(7q² - 2q + 1)/(q-1)³`;
* `expect1_rpow_two_le`, `expect1_rpow_three_le` : the same bounds with `Real.rpow` exponents.

**Checker form** (any real `θ ≥ 0`, in particular `θ = 5/2`): `expect1_rpow_le`
`E_γ[(v+1)^θ] ≤ 1 + ν (1 - 1/q) B` for every `γ`, as soon as
`B ≥ Σ_{a<K} x^{a+1}((a+2)^θ - 1) + x^{K+1}(K+2)^θ/(1-r)` where `((K+3)/(K+2))^θ · x ≤ r < 1`.
(This is exactly the partial sum `Σ_{a=1}^{K} q^{-a}((a+1)^θ - 1)` plus the geometric tail bound
of `rigcert.c`'s `sum_theta_up`.)

Generic tools: `expect1_eq_geom` (exact tail formula), `abel_partial`, `expect1_le_partial`,
`expect1_le_of_partial_bound`, `decay_of_ratio`, `partial_le_of_ratio`, `tendsto_of_ratio`.
-/

namespace MinModulus.Smooth

open Finset Filter Topology

variable {q : ℕ} {ν : ℝ}

/-! ### Generic machinery -/

/-- Exact tail formula: `E_γ[g] = g 0 + ν Σ_{r<γ} q^{-(r+1)} (g(r+1) - g r)`. -/
theorem expect1_eq_geom (q : ℕ) (ν : ℝ) (γ : ℕ) (g : ℕ → ℝ) :
    expect1 q ν γ g = g 0 + ν * ∑ r ∈ range γ, ((q : ℝ)⁻¹) ^ (r + 1) * (g (r + 1) - g r) := by
  rw [expect1_eq_tail, mul_sum]
  congr 1
  refine sum_congr rfl fun r _ => ?_
  rw [tailP_succ]
  ring

/-- Abel summation: the tail form versus the `(1 - x)` form. -/
theorem abel_partial (x : ℝ) (g : ℕ → ℝ) (N : ℕ) :
    ∑ r ∈ range N, x ^ (r + 1) * (g (r + 1) - g r) =
      (1 - x) * ∑ a ∈ range N, x ^ (a + 1) * (g (a + 1) - g 0) + x ^ (N + 1) * (g N - g 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih]
    ring

/-- For nondecreasing `g` and `γ ≤ N`:
`E_γ[g] ≤ g 0 + ν ((1-x) Σ_{a<N} x^{a+1}(g(a+1) - g 0) + x^{N+1}(g N - g 0))`. -/
theorem expect1_le_partial (hν : 0 ≤ ν) {g : ℕ → ℝ} (hg : Monotone g) {γ N : ℕ} (hγN : γ ≤ N) :
    expect1 q ν γ g ≤ g 0 + ν * ((1 - (q : ℝ)⁻¹) *
      ∑ a ∈ range N, ((q : ℝ)⁻¹) ^ (a + 1) * (g (a + 1) - g 0) +
      ((q : ℝ)⁻¹) ^ (N + 1) * (g N - g 0)) := by
  rw [expect1_eq_geom, ← abel_partial]
  have hx : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have hsub : ∑ r ∈ range γ, ((q : ℝ)⁻¹) ^ (r + 1) * (g (r + 1) - g r) ≤
      ∑ r ∈ range N, ((q : ℝ)⁻¹) ^ (r + 1) * (g (r + 1) - g r) :=
    sum_le_sum_of_subset_of_nonneg (range_mono hγN) fun r _ _ =>
      mul_nonneg (pow_nonneg hx _) (sub_nonneg.2 (hg (Nat.le_succ r)))
  have := mul_le_mul_of_nonneg_left hsub hν
  linarith

/-- If all partial sums `Σ_{a<N} x^{a+1}(g(a+1) - g 0)` are `≤ S` and `x^N g(N) → 0`, then
`E_γ[g] ≤ g 0 + ν (1 - x) S` for **every** cap `γ`. -/
theorem expect1_le_of_partial_bound (hq : 1 < q) (hν : 0 ≤ ν) {g : ℕ → ℝ} (hg : Monotone g)
    {S : ℝ} (hS : ∀ N, ∑ a ∈ range N, ((q : ℝ)⁻¹) ^ (a + 1) * (g (a + 1) - g 0) ≤ S)
    (hlim : Tendsto (fun N => ((q : ℝ)⁻¹) ^ N * g N) atTop (𝓝 0)) (γ : ℕ) :
    expect1 q ν γ g ≤ g 0 + ν * (1 - (q : ℝ)⁻¹) * S := by
  set x := (q : ℝ)⁻¹ with hx_def
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hq1
  have h1 : Tendsto (fun N => x ^ (N + 1) * (g N - g 0)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun N : ℕ => x * (x ^ N * g N) - x * x ^ N * g 0) atTop
        (𝓝 (x * 0 - x * 0 * g 0)) :=
      (hlim.const_mul x).sub
        (((tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1).const_mul x).mul_const (g 0))
    simp only [mul_zero, zero_mul, sub_zero] at h2
    refine h2.congr fun N => ?_
    ring
  have h3 : Tendsto (fun N => g 0 + ν * ((1 - x) * S + x ^ (N + 1) * (g N - g 0))) atTop
      (𝓝 (g 0 + ν * ((1 - x) * S + 0))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_const_nhds.add h1))
  rw [add_zero, ← mul_assoc] at h3
  refine ge_of_tendsto h3 (eventually_atTop.2 ⟨γ, fun N hN => ?_⟩)
  have h := expect1_le_partial (q := q) hν hg hN
  have h1x : 0 ≤ 1 - x := by linarith
  have h4 := mul_le_mul_of_nonneg_left (hS N) h1x
  have h5 := mul_le_mul_of_nonneg_left
    (add_le_add_right h4 (x ^ (N + 1) * (g N - g 0))) hν
  linarith

/-- Geometric decay from a ratio bound beyond `K`. -/
theorem decay_of_ratio {x r : ℝ} (hx0 : 0 ≤ x) (hr0 : 0 ≤ r) {g : ℕ → ℝ} (K : ℕ)
    (hratio : ∀ a, K + 1 ≤ a → x * g (a + 1) ≤ r * g a) (i : ℕ) :
    x ^ (K + 1 + i) * g (K + 1 + i) ≤ r ^ i * (x ^ (K + 1) * g (K + 1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := hratio (K + 1 + i) (Nat.le_add_right _ _)
    calc x ^ (K + 1 + (i + 1)) * g (K + 1 + (i + 1))
        = x ^ (K + 1 + i) * (x * g (K + 1 + i + 1)) := by
          rw [← add_assoc, pow_succ]; ring
      _ ≤ x ^ (K + 1 + i) * (r * g (K + 1 + i)) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg hx0 _)
      _ = r * (x ^ (K + 1 + i) * g (K + 1 + i)) := by ring
      _ ≤ r * (r ^ i * (x ^ (K + 1) * g (K + 1))) := mul_le_mul_of_nonneg_left ih hr0
      _ = r ^ (i + 1) * (x ^ (K + 1) * g (K + 1)) := by ring

/-- Partial sums are bounded by the first `K` terms plus the geometric tail bound. -/
theorem partial_le_of_ratio {x : ℝ} (hx0 : 0 ≤ x) {g : ℕ → ℝ} (hg : Monotone g) (hg0 : 0 ≤ g 0)
    (K : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hratio : ∀ a, K + 1 ≤ a → x * g (a + 1) ≤ r * g a) (N : ℕ) :
    ∑ a ∈ range N, x ^ (a + 1) * (g (a + 1) - g 0) ≤
      ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) + x ^ (K + 1) * g (K + 1) / (1 - r) := by
  have hf : ∀ a, 0 ≤ x ^ (a + 1) * (g (a + 1) - g 0) := fun a =>
    mul_nonneg (pow_nonneg hx0 _) (sub_nonneg.2 (hg (Nat.zero_le _)))
  have hG : 0 ≤ x ^ (K + 1) * g (K + 1) :=
    mul_nonneg (pow_nonneg hx0 _) (hg0.trans (hg (Nat.zero_le _)))
  have hterm : ∀ i, x ^ (K + i + 1) * (g (K + i + 1) - g 0) ≤
      r ^ i * (x ^ (K + 1) * g (K + 1)) := by
    intro i
    have e : K + i + 1 = K + 1 + i := by omega
    rw [e]
    have h1 : x ^ (K + 1 + i) * (g (K + 1 + i) - g 0) ≤ x ^ (K + 1 + i) * g (K + 1 + i) := by
      have := pow_nonneg hx0 (K + 1 + i)
      nlinarith
    exact h1.trans (decay_of_ratio hx0 hr0 K hratio i)
  have hgeom : ∑ i ∈ range N, r ^ i ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hr0 hr1
    rwa [← range_eq_Ico, pow_zero] at this
  calc ∑ a ∈ range N, x ^ (a + 1) * (g (a + 1) - g 0)
      ≤ ∑ a ∈ range (K + N), x ^ (a + 1) * (g (a + 1) - g 0) :=
        sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_add_left N K)) fun a _ _ => hf a
    _ = ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) +
          ∑ i ∈ range N, x ^ (K + i + 1) * (g (K + i + 1) - g 0) := sum_range_add _ _ _
    _ ≤ ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) +
          ∑ i ∈ range N, r ^ i * (x ^ (K + 1) * g (K + 1)) := by
        have := sum_le_sum fun i (_ : i ∈ range N) => hterm i
        linarith
    _ = ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) +
          (∑ i ∈ range N, r ^ i) * (x ^ (K + 1) * g (K + 1)) := by rw [sum_mul]
    _ ≤ ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) +
          1 / (1 - r) * (x ^ (K + 1) * g (K + 1)) := by
        have := mul_le_mul_of_nonneg_right hgeom hG
        linarith
    _ = ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) + x ^ (K + 1) * g (K + 1) / (1 - r) := by
        ring

/-- The ratio bound forces `x^N g(N) → 0`. -/
theorem tendsto_of_ratio {x : ℝ} (hx0 : 0 ≤ x) {g : ℕ → ℝ} (hg0 : ∀ a, 0 ≤ g a) (K : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hratio : ∀ a, K + 1 ≤ a → x * g (a + 1) ≤ r * g a) :
    Tendsto (fun N => x ^ N * g N) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat (K + 1)]
  have hlim : Tendsto (fun i : ℕ => r ^ i * (x ^ (K + 1) * g (K + 1))) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (x ^ (K + 1) * g (K + 1))
    simpa using this
  refine squeeze_zero (fun i => mul_nonneg (pow_nonneg hx0 _) (hg0 _)) (fun i => ?_) hlim
  rw [show i + (K + 1) = K + 1 + i by omega]
  exact decay_of_ratio hx0 hr0 K hratio i

/-! ### The checker form, any real `θ ≥ 0` -/

/-- **Uniform-in-γ bound, checker form.**  For real `θ ≥ 0`, `q > 1`, `ν ≥ 0`, any `K`, any
`r < 1` with `((K+3)/(K+2))^θ · q⁻¹ ≤ r`, and any
`B ≥ Σ_{a<K} q^{-(a+1)}((a+2)^θ - 1) + q^{-(K+1)} (K+2)^θ / (1 - r)`, we have for every cap `γ`
`E_γ[(v+1)^θ] ≤ 1 + ν (1 - q⁻¹) B`. -/
theorem expect1_rpow_le (hq : 1 < q) (hν : 0 ≤ ν) {θ : ℝ} (hθ : 0 ≤ θ) (K : ℕ) {r : ℝ}
    (hr : (((K : ℝ) + 3) / ((K : ℝ) + 2)) ^ θ * (q : ℝ)⁻¹ ≤ r) (hr1 : r < 1) {B : ℝ}
    (hB : ∑ a ∈ range K, ((q : ℝ)⁻¹) ^ (a + 1) * (((a : ℝ) + 2) ^ θ - 1) +
        ((q : ℝ)⁻¹) ^ (K + 1) * ((K : ℝ) + 2) ^ θ / (1 - r) ≤ B) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ θ) ≤ 1 + ν * (1 - (q : ℝ)⁻¹) * B := by
  set x := (q : ℝ)⁻¹ with hx_def
  set g : ℕ → ℝ := fun a => ((a : ℝ) + 1) ^ θ with hg_def
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hq1
  have hgnn : ∀ a, 0 ≤ g a := fun a => Real.rpow_nonneg (by positivity) θ
  have hgmono : Monotone g := by
    intro a b hab
    have : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    exact Real.rpow_le_rpow (by positivity) this hθ
  have hg0 : g 0 = 1 := by simp [hg_def]
  have hr0 : 0 ≤ r := le_trans (mul_nonneg (Real.rpow_nonneg (by positivity) θ) hx0) hr
  have hsucc : ∀ a : ℕ, g (a + 1) = ((a : ℝ) + 2) ^ θ := by
    intro a
    simp only [hg_def]
    congr 1
    push_cast
    ring
  have hratio : ∀ a, K + 1 ≤ a → x * g (a + 1) ≤ r * g a := by
    intro a ha
    have ha' : (K : ℝ) + 1 ≤ a := by exact_mod_cast ha
    have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hfrac : ((a : ℝ) + 2) / ((a : ℝ) + 1) ≤ ((K : ℝ) + 3) / ((K : ℝ) + 2) := by
      rw [div_le_div_iff₀ hpos (by positivity)]
      nlinarith
    have hga : g (a + 1) = (((a : ℝ) + 2) / ((a : ℝ) + 1)) ^ θ * g a := by
      rw [hsucc, hg_def]
      dsimp only
      rw [← Real.mul_rpow (by positivity) hpos.le, div_mul_cancel₀ _ hpos.ne']
    rw [hga]
    have hmono : (((a : ℝ) + 2) / ((a : ℝ) + 1)) ^ θ ≤ (((K : ℝ) + 3) / ((K : ℝ) + 2)) ^ θ :=
      Real.rpow_le_rpow (by positivity) hfrac hθ
    calc x * ((((a : ℝ) + 2) / ((a : ℝ) + 1)) ^ θ * g a)
        ≤ x * ((((K : ℝ) + 3) / ((K : ℝ) + 2)) ^ θ * g a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono (hgnn a)) hx0
      _ = ((((K : ℝ) + 3) / ((K : ℝ) + 2)) ^ θ * x) * g a := by ring
      _ ≤ r * g a := mul_le_mul_of_nonneg_right hr (hgnn a)
  have hS := partial_le_of_ratio hx0 hgmono (hgnn 0) K hr0 hr1 hratio
  have hlim := tendsto_of_ratio hx0 hgnn K hr0 hr1 hratio
  have hmain : expect1 q ν γ g ≤ g 0 + ν * (1 - x) *
      (∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) + x ^ (K + 1) * g (K + 1) / (1 - r)) :=
    expect1_le_of_partial_bound hq hν hgmono hS hlim γ
  have hSB : ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) + x ^ (K + 1) * g (K + 1) / (1 - r)
      ≤ B := by
    have e1 : ∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) =
        ∑ a ∈ range K, x ^ (a + 1) * (((a : ℝ) + 2) ^ θ - 1) :=
      sum_congr rfl fun a _ => by rw [hsucc, hg0]
    have e2 : g (K + 1) = ((K : ℝ) + 2) ^ θ := hsucc K
    rw [e1, e2]
    exact hB
  have hcoef : 0 ≤ ν * (1 - x) := mul_nonneg hν (by linarith)
  calc expect1 q ν γ g
      ≤ g 0 + ν * (1 - x) *
        (∑ a ∈ range K, x ^ (a + 1) * (g (a + 1) - g 0) + x ^ (K + 1) * g (K + 1) / (1 - r)) :=
        hmain
    _ ≤ g 0 + ν * (1 - x) * B := by
        have := mul_le_mul_of_nonneg_left hSB hcoef
        linarith
    _ = 1 + ν * (1 - x) * B := by rw [hg0]

/-! ### `θ = 2`: exact formula, uniform bound, limit -/

theorem sum_sq_identity (x : ℝ) (N : ℕ) :
    (∑ r ∈ range N, x ^ (r + 1) * (2 * (r : ℝ) + 3)) * (1 - x) ^ 2 =
      x * (3 - x) - x ^ (N + 1) * (2 + (2 * (N : ℝ) + 1) * (1 - x)) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

theorem sum_cube_identity (x : ℝ) (N : ℕ) :
    (∑ r ∈ range N, x ^ (r + 1) * (3 * (r : ℝ) ^ 2 + 9 * r + 7)) * (1 - x) ^ 3 =
      x * (7 - 2 * x + x ^ 2) - x ^ (N + 1) *
        (6 + 6 * (N : ℝ) * (1 - x) + (3 * (N : ℝ) ^ 2 + 3 * N + 1) * (1 - x) ^ 2) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

theorem one_sub_inv_pos (hq : 1 < q) : 0 < 1 - (q : ℝ)⁻¹ := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have := inv_lt_one_of_one_lt₀ hq1
  linarith

/-- Exact value for every cap: `E_γ[(v+1)²] = 1 + ν (x(3-x) - x^{γ+1}(2 + (2γ+1)(1-x)))/(1-x)²`. -/
theorem expect1_sq_eq (hq : 1 < q) (ν : ℝ) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 2) =
      1 + ν * (((q : ℝ)⁻¹ * (3 - (q : ℝ)⁻¹) - ((q : ℝ)⁻¹) ^ (γ + 1) *
        (2 + (2 * (γ : ℝ) + 1) * (1 - (q : ℝ)⁻¹))) / (1 - (q : ℝ)⁻¹) ^ 2) := by
  have hD : (1 - (q : ℝ)⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (one_sub_inv_pos hq).ne'
  rw [expect1_eq_geom, ← sum_sq_identity, mul_div_cancel_right₀ _ hD]
  simp only [Nat.cast_zero, zero_add, one_pow]
  congr 2
  refine sum_congr rfl fun r _ => ?_
  push_cast
  ring

theorem idealSq_eq (hq : 1 < q) :
    (q : ℝ)⁻¹ * (3 - (q : ℝ)⁻¹) / (1 - (q : ℝ)⁻¹) ^ 2 = (3 * q - 1) / ((q : ℝ) - 1) ^ 2 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq1' : (q : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- **θ = 2, uniform in the cap**: `E_γ[(v+1)²] ≤ 1 + ν(3q-1)/(q-1)²`. -/
theorem expect1_sq_le (hq : 1 < q) (hν : 0 ≤ ν) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ 1 + ν * (3 * q - 1) / ((q : ℝ) - 1) ^ 2 := by
  rw [expect1_sq_eq hq, mul_div_assoc, ← idealSq_eq hq]
  have hx0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have h1x := one_sub_inv_pos hq
  have hD : 0 < (1 - (q : ℝ)⁻¹) ^ 2 := by positivity
  have hC : 0 ≤ ((q : ℝ)⁻¹) ^ (γ + 1) * (2 + (2 * (γ : ℝ) + 1) * (1 - (q : ℝ)⁻¹)) := by
    positivity
  rw [sub_div, mul_sub]
  have : 0 ≤ ν * (((q : ℝ)⁻¹) ^ (γ + 1) * (2 + (2 * (γ : ℝ) + 1) * (1 - (q : ℝ)⁻¹)) /
      (1 - (q : ℝ)⁻¹) ^ 2) := mul_nonneg hν (div_nonneg hC hD.le)
  linarith

theorem tendsto_quad_mul_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (a b c : ℝ) :
    Tendsto (fun n : ℕ => x ^ (n + 1) * (a + b * n + c * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 habs
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 habs
  have h2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 habs
  have := (((h0.const_mul a).add (h1.const_mul b)).add (h2.const_mul c)).const_mul x
  simp only [mul_zero, add_zero] at this
  refine this.congr fun n => ?_
  simp only [pow_zero, pow_one, one_mul]
  ring

/-- **θ = 2, idealized closed form**: `E_γ[(v+1)²] → 1 + ν(3q-1)/(q-1)²` as `γ → ∞`. -/
theorem tendsto_expect1_sq (hq : 1 < q) (ν : ℝ) :
    Tendsto (fun γ => expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 2)) atTop
      (𝓝 (1 + ν * (3 * q - 1) / ((q : ℝ) - 1) ^ 2)) := by
  set x := (q : ℝ)⁻¹ with hx_def
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hq1
  have hc := tendsto_quad_mul_pow hx0 hx1 (2 + (1 - x)) (2 * (1 - x)) 0
  have hlim : Tendsto (fun γ : ℕ => 1 + ν * ((x * (3 - x) - x ^ (γ + 1) *
      (2 + (2 * (γ : ℝ) + 1) * (1 - x))) / (1 - x) ^ 2)) atTop
      (𝓝 (1 + ν * ((x * (3 - x) - 0) / (1 - x) ^ 2))) := by
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
    refine Tendsto.div_const (tendsto_const_nhds.sub (hc.congr fun n => ?_)) _
    ring
  rw [sub_zero, idealSq_eq hq, ← mul_div_assoc] at hlim
  refine hlim.congr fun γ => ?_
  rw [expect1_sq_eq hq]

/-! ### `θ = 3`: exact formula, uniform bound, limit -/

/-- Exact value for every cap:
`E_γ[(v+1)³] = 1 + ν (x(7-2x+x²) - x^{γ+1}(6 + 6γ(1-x) + (3γ²+3γ+1)(1-x)²))/(1-x)³`. -/
theorem expect1_cube_eq (hq : 1 < q) (ν : ℝ) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 3) =
      1 + ν * (((q : ℝ)⁻¹ * (7 - 2 * (q : ℝ)⁻¹ + ((q : ℝ)⁻¹) ^ 2) - ((q : ℝ)⁻¹) ^ (γ + 1) *
        (6 + 6 * (γ : ℝ) * (1 - (q : ℝ)⁻¹) + (3 * (γ : ℝ) ^ 2 + 3 * γ + 1) *
          (1 - (q : ℝ)⁻¹) ^ 2)) / (1 - (q : ℝ)⁻¹) ^ 3) := by
  have hD : (1 - (q : ℝ)⁻¹) ^ 3 ≠ 0 := pow_ne_zero 3 (one_sub_inv_pos hq).ne'
  rw [expect1_eq_geom, ← sum_cube_identity, mul_div_cancel_right₀ _ hD]
  simp only [Nat.cast_zero, zero_add, one_pow]
  congr 2
  refine sum_congr rfl fun r _ => ?_
  push_cast
  ring

theorem idealCube_eq (hq : 1 < q) :
    (q : ℝ)⁻¹ * (7 - 2 * (q : ℝ)⁻¹ + ((q : ℝ)⁻¹) ^ 2) / (1 - (q : ℝ)⁻¹) ^ 3 =
      (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq1' : (q : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- **θ = 3, uniform in the cap**: `E_γ[(v+1)³] ≤ 1 + ν(7q² - 2q + 1)/(q-1)³`. -/
theorem expect1_cube_le (hq : 1 < q) (hν : 0 ≤ ν) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 3) ≤
      1 + ν * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 := by
  rw [expect1_cube_eq hq, mul_div_assoc, ← idealCube_eq hq]
  have hx0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have h1x := one_sub_inv_pos hq
  have hD : 0 < (1 - (q : ℝ)⁻¹) ^ 3 := by positivity
  have hC : 0 ≤ ((q : ℝ)⁻¹) ^ (γ + 1) * (6 + 6 * (γ : ℝ) * (1 - (q : ℝ)⁻¹) +
      (3 * (γ : ℝ) ^ 2 + 3 * γ + 1) * (1 - (q : ℝ)⁻¹) ^ 2) := by
    positivity
  rw [sub_div, mul_sub]
  have : 0 ≤ ν * (((q : ℝ)⁻¹) ^ (γ + 1) * (6 + 6 * (γ : ℝ) * (1 - (q : ℝ)⁻¹) +
      (3 * (γ : ℝ) ^ 2 + 3 * γ + 1) * (1 - (q : ℝ)⁻¹) ^ 2) / (1 - (q : ℝ)⁻¹) ^ 3) :=
    mul_nonneg hν (div_nonneg hC hD.le)
  linarith

/-- **θ = 3, idealized closed form**: `E_γ[(v+1)³] → 1 + ν(7q² - 2q + 1)/(q-1)³` as `γ → ∞`. -/
theorem tendsto_expect1_cube (hq : 1 < q) (ν : ℝ) :
    Tendsto (fun γ => expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 3)) atTop
      (𝓝 (1 + ν * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3)) := by
  set x := (q : ℝ)⁻¹ with hx_def
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hq1
  have hc := tendsto_quad_mul_pow hx0 hx1 (6 + (1 - x) ^ 2) (6 * (1 - x) + 3 * (1 - x) ^ 2)
    (3 * (1 - x) ^ 2)
  have hlim : Tendsto (fun γ : ℕ => 1 + ν * ((x * (7 - 2 * x + x ^ 2) - x ^ (γ + 1) *
      (6 + 6 * (γ : ℝ) * (1 - x) + (3 * (γ : ℝ) ^ 2 + 3 * γ + 1) * (1 - x) ^ 2)) /
        (1 - x) ^ 3)) atTop
      (𝓝 (1 + ν * ((x * (7 - 2 * x + x ^ 2) - 0) / (1 - x) ^ 3))) := by
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
    refine Tendsto.div_const (tendsto_const_nhds.sub (hc.congr fun n => ?_)) _
    ring
  rw [sub_zero, idealCube_eq hq, ← mul_div_assoc] at hlim
  refine hlim.congr fun γ => ?_
  rw [expect1_cube_eq hq]

/-! ### `Real.rpow` versions for `θ = 2, 3` -/

theorem rpow_natCast_add_one (a : ℕ) (k : ℕ) : ((a : ℝ) + 1) ^ (k : ℝ) = ((a : ℝ) + 1) ^ k :=
  Real.rpow_natCast _ k

theorem expect1_rpow_two_le (hq : 1 < q) (hν : 0 ≤ ν) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (2 : ℝ)) ≤
      1 + ν * (3 * q - 1) / ((q : ℝ) - 1) ^ 2 := by
  simp_rw [Real.rpow_two]
  exact expect1_sq_le hq hν γ

theorem expect1_rpow_three_le (hq : 1 < q) (hν : 0 ≤ ν) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (3 : ℝ)) ≤
      1 + ν * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 := by
  have h : ∀ a : ℕ, ((a : ℝ) + 1) ^ (3 : ℝ) = ((a : ℝ) + 1) ^ 3 := fun a => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [h]
  exact expect1_cube_le hq hν γ

end MinModulus.Smooth
