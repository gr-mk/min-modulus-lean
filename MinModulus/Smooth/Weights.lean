import MinModulus.Smooth.Tau
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Module 4 (`Smooth`), part 4: the weights `w_p` and `U_p`

For a prime `p` (any `p > 1` suffices) and a threshold `m`:
* `j0 p m d` = the least `j ≥ 1` with `d · p^j ≥ m` (computable, via `Nat.find`; junk value `1`
  when `p ≤ 1` or `d = 0`).  Characterizations: `j0_le_iff`, `lt_j0_iff`, `j0_eq_of`.
* `wp p m d = p^{1 - j0(d)} / (p - 1)`, written `(p⁻¹)^(j0 - 1) / (p - 1)`; it equals
  `Σ_{j ≥ j0} p^{-j}` (`hasSum_wp`), and every finite sum of `p^{-j}` over distinct admissible
  `j` (`j ≥ 1`, `d p^j ≥ m`) is `≤ wp p m d` (`sum_le_wp`).
* `Up p m s = Σ_{d ∣ s} wp p m d`.

Main results: (vi) `wp_le : wp p m d ≤ 1/(p-1)`, `Up_le_card_div : U_p(s) ≤ τ(s)/(p-1)`; plus
`sum_pairs_le_Up` (the enlargement inequality in abstract form), `Up_mono`, `monotone_Up_smooth`,
and the splitting bound `Up_mul_le : U_p(ab) ≤ U_p(a) + (τ(b)-1) τ(a)/(p-1)` for coprime `a, b`.
-/

namespace MinModulus.Smooth

open Finset

theorem exists_le_mul_pow_succ {p d : ℕ} (hp : 1 < p) (hd : 0 < d) (m : ℕ) :
    ∃ j, m ≤ d * p ^ (j + 1) := by
  refine ⟨m, ?_⟩
  calc m ≤ p ^ m := (Nat.lt_pow_self hp).le
    _ ≤ p ^ (m + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ m)
    _ ≤ d * p ^ (m + 1) := Nat.le_mul_of_pos_left _ hd

/-- `j0 p m d = min {j ≥ 1 : d · p^j ≥ m}` for `p > 1`, `d > 0` (junk value `1` otherwise). -/
def j0 (p m d : ℕ) : ℕ :=
  if h : 1 < p ∧ 0 < d then Nat.find (exists_le_mul_pow_succ h.1 h.2 m) + 1 else 1

/-- `w_p(d) = p^{1 - j0(d)} / (p - 1) = Σ_{j ≥ j0(d)} p^{-j}`. -/
noncomputable def wp (p m d : ℕ) : ℝ :=
  ((p : ℝ)⁻¹) ^ (j0 p m d - 1) / ((p : ℝ) - 1)

/-- `U_p(s) = Σ_{d ∣ s} w_p(d)`. -/
noncomputable def Up (p m s : ℕ) : ℝ :=
  ∑ d ∈ s.divisors, wp p m d

variable {p m d j : ℕ}

/-! ### `j0` -/

theorem one_le_j0 (p m d : ℕ) : 1 ≤ j0 p m d := by
  unfold j0
  split_ifs <;> omega

theorem le_mul_pow_j0 (hp : 1 < p) (hd : 0 < d) : m ≤ d * p ^ j0 p m d := by
  rw [j0, dite_eq_left ⟨hp, hd⟩]
  exact Nat.find_spec (exists_le_mul_pow_succ hp hd m)

theorem j0_le_of (hp : 1 < p) (hd : 0 < d) (hj : 1 ≤ j) (h : m ≤ d * p ^ j) : j0 p m d ≤ j := by
  rw [j0, dite_eq_left ⟨hp, hd⟩]
  have : Nat.find (exists_le_mul_pow_succ hp hd m) ≤ j - 1 :=
    Nat.find_min' _ (by rwa [Nat.sub_add_cancel hj])
  omega

/-- For `j ≥ 1`: `j0 ≤ j ↔ m ≤ d p^j`. -/
theorem j0_le_iff (hp : 1 < p) (hd : 0 < d) (hj : 1 ≤ j) : j0 p m d ≤ j ↔ m ≤ d * p ^ j :=
  ⟨fun h => (le_mul_pow_j0 hp hd).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h)), j0_le_of hp hd hj⟩

/-- For `j ≥ 1`: `j < j0 ↔ d p^j < m`. -/
theorem lt_j0_iff (hp : 1 < p) (hd : 0 < d) (hj : 1 ≤ j) : j < j0 p m d ↔ d * p ^ j < m := by
  rw [← not_le, j0_le_iff hp hd hj, not_le]

/-- Certificate form: `j0 p m d = j` as soon as `1 ≤ j`, `m ≤ d p^j`, and either `j = 1` or
`d p^{j-1} < m`. -/
theorem j0_eq_of (hp : 1 < p) (hd : 0 < d) (hj : 1 ≤ j) (h : m ≤ d * p ^ j)
    (hmin : j = 1 ∨ d * p ^ (j - 1) < m) : j0 p m d = j := by
  apply le_antisymm (j0_le_of hp hd hj h)
  rcases hmin with rfl | hlt
  · exact one_le_j0 p m d
  · by_contra hcon
    have h1 : j0 p m d ≤ j - 1 := by omega
    have h2 : 1 ≤ j - 1 := le_trans (one_le_j0 p m d) h1
    have := (j0_le_iff hp hd h2).1 h1
    omega

/-- `j0` is antitone in `d`. -/
theorem j0_anti (hp : 1 < p) (hd : 0 < d) {d' : ℕ} (hdd : d ≤ d') : j0 p m d' ≤ j0 p m d :=
  j0_le_of hp (lt_of_lt_of_le hd hdd) (one_le_j0 p m d)
    ((le_mul_pow_j0 hp hd).trans (Nat.mul_le_mul_right _ hdd))

/-! ### `w_p` -/

theorem one_lt_cast (hp : 1 < p) : (1 : ℝ) < p := by exact_mod_cast hp

theorem wp_nonneg (hp : 1 < p) (m d : ℕ) : 0 ≤ wp p m d := by
  have := one_lt_cast hp
  unfold wp
  exact div_nonneg (pow_nonneg (by positivity) _) (by linarith)

theorem wp_pos (hp : 1 < p) (m d : ℕ) : 0 < wp p m d := by
  have := one_lt_cast hp
  unfold wp
  exact div_pos (pow_pos (by positivity) _) (by linarith)

/-- (vi) `w_p(d) ≤ 1/(p - 1)`. -/
theorem wp_le (hp : 1 < p) (m d : ℕ) : wp p m d ≤ 1 / ((p : ℝ) - 1) := by
  have := one_lt_cast hp
  unfold wp
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact pow_le_one₀ (by positivity) (natCast_inv_le_one p)

/-- `w_p(d) = p^{-j0}/(1 - p^{-1})`. -/
theorem wp_eq_pow_div (hp : 1 < p) (m d : ℕ) :
    wp p m d = ((p : ℝ)⁻¹) ^ j0 p m d / (1 - (p : ℝ)⁻¹) := by
  have hp1 := one_lt_cast hp
  have hj := one_le_j0 p m d
  unfold wp
  obtain ⟨k, hk⟩ : ∃ k, j0 p m d = k + 1 := ⟨j0 p m d - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- `w_p(d) = Σ_{j ≥ j0(d)} p^{-j}`. -/
theorem hasSum_wp (hp : 1 < p) (m d : ℕ) :
    HasSum (fun i : ℕ => ((p : ℝ)⁻¹) ^ (j0 p m d + i)) (wp p m d) := by
  have hp1 := one_lt_cast hp
  have hx0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  rw [wp_eq_pow_div hp, div_eq_mul_inv]
  simp_rw [pow_add]
  exact (hasSum_geometric_of_lt_one hx0 hx1).mul_left _

/-- Any finite sum of `p^{-j}` over admissible exponents `j` (`j ≥ 1`, `d p^j ≥ m`) is at most
`w_p(d)`. -/
theorem sum_le_wp (hp : 1 < p) (hd : 0 < d) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ m ≤ d * p ^ j) :
    ∑ j ∈ J, ((p : ℝ)⁻¹) ^ j ≤ wp p m d := by
  have hp1 := one_lt_cast hp
  have hx0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hsub : J ⊆ Ico (j0 p m d) (J.sup id + 1) := by
    intro j hj
    rw [mem_Ico]
    exact ⟨j0_le_of hp hd (hJ j hj).1 (hJ j hj).2,
      Nat.lt_succ_of_le (le_sup (f := id) hj)⟩
  calc ∑ j ∈ J, ((p : ℝ)⁻¹) ^ j ≤ ∑ j ∈ Ico (j0 p m d) (J.sup id + 1), ((p : ℝ)⁻¹) ^ j :=
        sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => pow_nonneg hx0 j
    _ ≤ ((p : ℝ)⁻¹) ^ j0 p m d / (1 - (p : ℝ)⁻¹) := geom_sum_Ico_le_of_lt_one hx0 hx1
    _ = wp p m d := (wp_eq_pow_div hp m d).symm

/-! ### `U_p` -/

theorem Up_nonneg (hp : 1 < p) (m s : ℕ) : 0 ≤ Up p m s :=
  sum_nonneg fun d _ => wp_nonneg hp m d

/-- (vi) `U_p(s) ≤ τ(s)/(p - 1)`. -/
theorem Up_le_card_div (hp : 1 < p) (m s : ℕ) :
    Up p m s ≤ (s.divisors.card : ℝ) / ((p : ℝ) - 1) := by
  unfold Up
  calc ∑ d ∈ s.divisors, wp p m d ≤ ∑ _d ∈ s.divisors, 1 / ((p : ℝ) - 1) :=
        sum_le_sum fun d _ => wp_le hp m d
    _ = (s.divisors.card : ℝ) / ((p : ℝ) - 1) := by rw [sum_const, nsmul_eq_mul]; ring

/-- `U_p` is monotone for divisibility. -/
theorem Up_mono (hp : 1 < p) (m : ℕ) {s s' : ℕ} (h : s ∣ s') (hs' : s' ≠ 0) :
    Up p m s ≤ Up p m s' :=
  sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hs' h) fun d _ _ => wp_nonneg hp m d

/-- `v ↦ U_p(s(v))` is monotone (coordinatewise), so the monotone coupling applies to any
nondecreasing function of it. -/
theorem monotone_Up_smooth (hp : 1 < p) (m : ℕ) {Ps : Finset ℕ} (hPs : ∀ q ∈ Ps, 0 < q) :
    Monotone (fun v => Up p m (smooth Ps v)) :=
  fun _ w hvw => Up_mono hp m (smooth_dvd_smooth fun q _ => hvw q) (smooth_ne_zero hPs w)

/-- **Enlargement, abstract form.**  If `T` is a finite set of pairs `(d, j)` with `d ∣ s`,
`j ≥ 1` and `d p^j ≥ m`, then `Σ_{(d,j) ∈ T} p^{-j} ≤ U_p(s)`. -/
theorem sum_pairs_le_Up (hp : 1 < p) {s : ℕ} (hs : s ≠ 0) (T : Finset (ℕ × ℕ))
    (hT : ∀ x ∈ T, x.1 ∣ s ∧ 1 ≤ x.2 ∧ m ≤ x.1 * p ^ x.2) :
    ∑ x ∈ T, ((p : ℝ)⁻¹) ^ x.2 ≤ Up p m s := by
  unfold Up
  rw [← sum_fiberwise_of_maps_to (g := Prod.fst) (t := s.divisors)
    (fun x hx => Nat.mem_divisors.2 ⟨(hT x hx).1, hs⟩)]
  refine sum_le_sum fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hinj : ∀ x ∈ T.filter (fun x => x.1 = d), ∀ y ∈ T.filter (fun x => x.1 = d),
      x.2 = y.2 → x = y := by
    intro x hx y hy hxy
    rw [mem_filter] at hx hy
    exact Prod.ext (hx.2.trans hy.2.symm) hxy
  rw [← sum_image (g := Prod.snd) hinj]
  apply sum_le_wp hp hd0
  intro j hj
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hj
  rw [mem_filter] at hx
  obtain ⟨hxT, hx1⟩ := hx
  have := hT x hxT
  exact ⟨this.2.1, hx1 ▸ this.2.2⟩

/-- **Splitting bound** used by the checker: for coprime `a, b`,
`U_p(ab) ≤ U_p(a) + (τ(b) - 1) τ(a)/(p - 1)`. -/
theorem Up_mul_le (hp : 1 < p) (m : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0)
    (hb : b ≠ 0) :
    Up p m (a * b) ≤ Up p m a +
      ((b.divisors.card : ℝ) - 1) * (a.divisors.card : ℝ) / ((p : ℝ) - 1) := by
  have hp1 := one_lt_cast hp
  have hsub : a.divisors ⊆ (a * b).divisors :=
    Nat.divisors_subset_of_dvd (Nat.mul_ne_zero ha hb) (dvd_mul_right a b)
  unfold Up
  rw [← sum_sdiff hsub]
  have hcard : ((((a * b).divisors \ a.divisors).card : ℕ) : ℝ) =
      ((b.divisors.card : ℝ) - 1) * (a.divisors.card : ℝ) := by
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub),
      Nat.Coprime.card_divisors_mul hab]
    push_cast
    ring
  have : ∑ x ∈ (a * b).divisors \ a.divisors, wp p m x ≤
      ((b.divisors.card : ℝ) - 1) * (a.divisors.card : ℝ) / ((p : ℝ) - 1) := by
    calc ∑ x ∈ (a * b).divisors \ a.divisors, wp p m x
        ≤ ∑ _x ∈ (a * b).divisors \ a.divisors, 1 / ((p : ℝ) - 1) :=
          sum_le_sum fun d _ => wp_le hp m d
      _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]; ring
  linarith

end MinModulus.Smooth
