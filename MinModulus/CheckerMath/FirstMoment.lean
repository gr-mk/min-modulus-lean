import MinModulus.CheckerMath.HingeTilt

/-!
# CheckerMath: the first-moment bound (primes with `δ_p = 0`)

STATUS: complete, no `sorry`. Owned by the CheckerMath (first moment / moments / glue) agent.

For `δ_p = 0` the hinge loss is the first moment `E_γ[U_p(s)]`. Write `x = 1/p` and
`w_p(d) = 1/(p-1) - e(d)` with `e(d) = Σ_{j ≥ 1, d p^j < m} p^{-j} ≥ 0`. Then
`E_γ[U_p(s)] = Σ_{b ≤ γ} w_p(s(b)) P(s(b) ∣ s)` (`Smooth.expect_Up_eq`), and

  `E_γ[U_p(s)] ≤ (Π_{q} (1 + ν_q/(q-1)))/(p-1) - Σ_{n ∈ D} ν(n)/n · (1 - p^{-J(n)})/(p-1)`

for **every** cap `γ`, every finite set `D` of positive `Ps`-smooth integers, and every `J` with
`n p^{J(n)} < m` (`J(n) = 0` allowed). Here `ν(n) = Π_{q ∣ n} ν_q` (`nuD`). This is rigcert's
`M1 = T1/(p-1) - U1`, `U1 = Σ_{n < ⌈m/p⌉ smooth} ν(n) c(n)/n`, `c(n) = Σ_{j ≤ J(n)} p^{-j}`
`= (1 - p^{-J(n)})/(p-1)`, `J(n) = #{j ≥ 1 : n < ⌈m/p^j⌉}`; swapping the sums gives the form
`Σ_{j≥1} p^{-j} (T1 - Σ_{d < ⌈m/p^j⌉ smooth} ν(d)/d)`. (rigcert rounds `T1` up and the
subtracted partial Euler sum `U1` down; the real statement below is the exact inequality.)

Main results:
* `expect_Up_le_firstMoment` : the bound above for an arbitrary set of primes `Ps`, tilts
  `0 ≤ ν ≤ q`, all caps;
* `hingeLoss_le_firstMoment` : the certificate form, `δ p = 0`, tilt upper bounds
  `tilt δ q ≤ ν q ≤ q` below `p`;
* `hingeLoss_le_firstMoment_of_zero` : all `δ_q = 0` below `p` (so `ν ≡ 1`), in exactly the
  arithmetic form of `CheckerImpl.firstMoment`:
  `(Π q)/((Π (q-1))(p-1)) - Σ_{n ∈ D} (p^{J n} - 1)/((p-1) p^{J n} n)`.
Helpers: `sum_box_prod` (a sum over the box of a product is the product of the sums),
`sum_tailP_le`, `smooth_expo`, `expo_mem_box`, `prod_tailP_expo` (`P(n ∣ s) = ν(n)/n`),
`wp_le_of_mul_pow_lt`, `primeFactors_smooth_subset` (smoothness of `n = Π_{q∈Ps} q^{e q}`).
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth MinModulus.Main

/-- `ν(n) = Π_{q ∣ n prime} ν_q`. -/
noncomputable def nuD (ν : ℕ → ℝ) (n : ℕ) : ℝ := ∏ q ∈ n.primeFactors, ν q

/-- The exponent vector of `n` (its factorization, as a function). -/
def expo (n : ℕ) : ℕ → ℕ := fun q => n.factorization q

theorem nuD_one_eq (n : ℕ) : nuD (fun _ => 1) n = 1 := by simp [nuD]

theorem nuD_nonneg {ν : ℕ → ℝ} {n : ℕ} (h : ∀ q ∈ n.primeFactors, 0 ≤ ν q) : 0 ≤ nuD ν n :=
  prod_nonneg h

/-! ### A sum over the box of a product is the product of the sums -/

theorem sum_box_prod (Ps : Finset ℕ) (γ : ℕ → ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ b ∈ box Ps γ, ∏ q ∈ Ps, f q (b q) = ∏ q ∈ Ps, ∑ a ∈ range (γ q + 1), f q a := by
  rw [prod_sum Ps (fun q => range (γ q + 1)) f]
  unfold box
  rw [sum_map]
  refine sum_congr rfl fun g _ => ?_
  rw [← prod_attach Ps]
  refine prod_congr rfl fun x _ => ?_
  simp [extendZero, x.2]

/-- `Σ_{a ≤ γ} P(V ≥ a) ≤ 1 + ν/(q-1)` (i.e. `E[min(V,γ) + 1] ≤ E[V + 1]`). -/
theorem sum_tailP_le {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) (γ : ℕ) :
    ∑ a ∈ range (γ + 1), tailP q ν a ≤ 1 + ν / ((q : ℝ) - 1) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  set x : ℝ := (q : ℝ)⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hq1
  rw [sum_range_succ', tailP_zero]
  simp_rw [tailP_succ]
  have hg : ∑ a ∈ range γ, x ^ a ≤ 1 / (1 - x) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := γ) hx0 hx1
    rwa [← range_eq_Ico, pow_zero] at this
  have e1 : ∑ a ∈ range γ, ν * x ^ (a + 1) = ν * x * ∑ a ∈ range γ, x ^ a := by
    rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  have e2 : ν * x * (1 / (1 - x)) = ν / ((q : ℝ) - 1) := by
    rw [hx]
    field_simp
  have h3 : ν * x * ∑ a ∈ range γ, x ^ a ≤ ν * x * (1 / (1 - x)) :=
    mul_le_mul_of_nonneg_left hg (mul_nonneg hν hx0)
  linarith

/-! ### The exponent vector of a smooth number -/

section Expo

variable {Ps : Finset ℕ} {n : ℕ}

theorem expo_eq_zero_of_notMem (hsub : n.primeFactors ⊆ Ps) {r : ℕ} (hr : r ∉ Ps) :
    expo n r = 0 := by
  have : r ∉ n.factorization.support := by
    rw [Nat.support_factorization]
    exact fun h => hr (hsub h)
  exact Finsupp.notMem_support_iff.1 this

theorem smooth_expo (hPs : ∀ q ∈ Ps, q.Prime) (hn : n ≠ 0) (hsub : n.primeFactors ⊆ Ps) :
    smooth Ps (expo n) = n := by
  apply Nat.eq_of_factorization_eq (smooth_ne_zero (fun q hq => (hPs q hq).pos) _) hn
  intro r
  rw [factorization_smooth hPs]
  split_ifs with hr
  · rfl
  · exact (expo_eq_zero_of_notMem hsub hr).symm

theorem expo_mem_box (hn : n ≠ 0) (hsub : n.primeFactors ⊆ Ps) {γ : ℕ → ℕ}
    (hγ : ∀ q ∈ Ps, n ≤ γ q) : expo n ∈ box Ps γ :=
  mem_box.2 ⟨fun q hq => (Nat.factorization_lt q hn).le.trans (hγ q hq),
    fun _ hq => expo_eq_zero_of_notMem hsub hq⟩

/-- Smooth numbers have their prime factors in `Ps`: `(s(e)).primeFactors ⊆ Ps` (to discharge
the smoothness hypothesis of the first-moment bounds from a factorization `n = Π_{q∈Ps} q^{e q}`). -/
theorem primeFactors_smooth_subset (hPs : ∀ q ∈ Ps, q.Prime) (e : ℕ → ℕ) :
    (smooth Ps e).primeFactors ⊆ Ps := by
  intro r hr
  by_contra hrP
  have h1 : (smooth Ps e).factorization r = 0 := by
    rw [factorization_smooth hPs, ite_eq_right hrP]
  rw [← Nat.support_factorization] at hr
  exact Finsupp.mem_support_iff.1 hr h1

/-- `tailP q ν a = (if a = 0 then 1 else ν) · q^{-a}`. -/
theorem tailP_eq_ite_mul (q : ℕ) (ν : ℝ) (a : ℕ) :
    tailP q ν a = (if a = 0 then 1 else ν) * ((q : ℝ)⁻¹) ^ a := by
  unfold tailP
  split_ifs with h
  · simp [h]
  · rfl

/-- `P(n ∣ s) = Π_{q ∈ Ps} P(V_q ≥ v_q(n)) = ν(n)/n` for `Ps`-smooth `n ≥ 1`. -/
theorem prod_tailP_expo (hPs : ∀ q ∈ Ps, q.Prime) (hn : n ≠ 0) (hsub : n.primeFactors ⊆ Ps)
    (ν : ℕ → ℝ) : ∏ q ∈ Ps, tailP q (ν q) (expo n q) = nuD ν n / n := by
  simp_rw [tailP_eq_ite_mul]
  rw [prod_mul_distrib]
  have h1 : ∏ q ∈ Ps, (if expo n q = 0 then (1 : ℝ) else ν q) = nuD ν n := by
    rw [← prod_filter_not_mul_prod_filter Ps (fun q => expo n q = 0)]
    have ha : ∏ q ∈ Ps with ¬ expo n q = 0, (if expo n q = 0 then (1 : ℝ) else ν q) =
        ∏ q ∈ Ps with ¬ expo n q = 0, ν q :=
      prod_congr rfl fun q hq => by rw [ite_eq_right (mem_filter.1 hq).2]
    have hb : ∏ q ∈ Ps with expo n q = 0, (if expo n q = 0 then (1 : ℝ) else ν q) = 1 :=
      prod_eq_one fun q hq => by rw [ite_eq_left (mem_filter.1 hq).2]
    have hc : Ps.filter (fun q => ¬ expo n q = 0) = n.primeFactors := by
      ext q
      simp only [mem_filter]
      constructor
      · rintro ⟨_, hq⟩
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.2 hq
      · intro hq
        refine ⟨hsub hq, ?_⟩
        rw [← Nat.support_factorization] at hq
        exact Finsupp.mem_support_iff.1 hq
    rw [ha, hb, hc, mul_one]
    rfl
  have h2 : ∏ q ∈ Ps, ((q : ℝ)⁻¹) ^ expo n q = (n : ℝ)⁻¹ := by
    simp_rw [inv_pow]
    rw [prod_inv_distrib]
    congr 1
    have := smooth_expo hPs hn hsub
    unfold smooth at this
    exact_mod_cast this
  rw [h1, h2, div_eq_mul_inv]

end Expo

/-! ### The weight of a divisor below the threshold -/

/-- If `n p^J < m` (or `J = 0`), then `w_p(n) ≤ p^{-J}/(p-1)`. -/
theorem wp_le_of_mul_pow_lt {p m n J : ℕ} (hp : 1 < p) (hn : 0 < n) (hJ : J ≠ 0 → n * p ^ J < m) :
    wp p m n ≤ ((p : ℝ)⁻¹) ^ J / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hx0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1.le
  have hJle : J ≤ j0 p m n - 1 := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have := (lt_j0_iff hp hn hpos).2 (hJ hpos.ne')
      omega
  unfold wp
  exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hx0 hx1 hJle) (by linarith)

/-! ### The first-moment bound -/

/-- **First moment, uniform in the caps.** For primes `Ps`, tilts `0 ≤ ν ≤ q`, a finite set `D`
of positive `Ps`-smooth integers and exponents `J` with `n p^{J n} < m` (unless `J n = 0`):
`E_γ[U_p(s)] ≤ (Π_{q∈Ps} (1 + ν_q/(q-1)))/(p-1) - Σ_{n∈D} ν(n)/n · (1 - p^{-J n})/(p-1)`. -/
theorem expect_Up_le_firstMoment {Ps : Finset ℕ} (hPs : ∀ q ∈ Ps, q.Prime) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) {p m : ℕ} (hp : 1 < p) (D : Finset ℕ)
    (hD : ∀ n ∈ D, 0 < n ∧ n.primeFactors ⊆ Ps) (J : ℕ → ℕ)
    (hJ : ∀ n ∈ D, J n ≠ 0 → n * p ^ J n < m) (γ : ℕ → ℕ) :
    expect Ps ν γ (fun v => Up p m (smooth Ps v)) ≤
      (∏ q ∈ Ps, (1 + ν q / ((q : ℝ) - 1))) / ((p : ℝ) - 1) -
        ∑ n ∈ D, nuD ν n / n * ((1 - ((p : ℝ)⁻¹) ^ J n) / ((p : ℝ) - 1)) := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  set K := D.sup id with hK
  refine expect_le_of_forall_ge_cap hν
    (monotone_Up_smooth hp m (fun q hq => (hPs q hq).pos)) (fun _ => K) (fun γ' hγ' => ?_) γ
  rw [expect_Up_eq hPs ν γ' p m]
  set π : (ℕ → ℕ) → ℝ := fun b => ∏ q ∈ Ps, tailP q (ν q) (b q) with hπ
  set e : ℕ → ℝ := fun d => 1 / ((p : ℝ) - 1) - wp p m d with he
  have hπ0 : ∀ b, 0 ≤ π b := fun b =>
    prod_nonneg fun q hq => tailP_nonneg (hν q hq).1 q _
  have he0 : ∀ d, 0 ≤ e d := fun d => sub_nonneg.2 (wp_le hp m d)
  have hsplit : ∑ b ∈ box Ps γ', wp p m (smooth Ps b) * π b =
      1 / ((p : ℝ) - 1) * ∑ b ∈ box Ps γ', π b - ∑ b ∈ box Ps γ', e (smooth Ps b) * π b := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    simp only [he]
    ring
  -- the full Euler product
  have h1 : ∑ b ∈ box Ps γ', π b ≤ ∏ q ∈ Ps, (1 + ν q / ((q : ℝ) - 1)) := by
    rw [hπ, sum_box_prod Ps γ' (fun q a => tailP q (ν q) a)]
    refine prod_le_prod₀ (fun q hq => sum_nonneg fun a _ => tailP_nonneg (hν q hq).1 q a)
      fun q hq => sum_tailP_le (hPs q hq).one_lt (hν q hq).1 (γ' q)
  -- the subtracted partial Euler sum
  have hexpo : ∀ n ∈ D, smooth Ps (expo n) = n := fun n hn =>
    smooth_expo hPs (hD n hn).1.ne' (hD n hn).2
  have h2 : ∑ n ∈ D, nuD ν n / n * ((1 - ((p : ℝ)⁻¹) ^ J n) / ((p : ℝ) - 1)) ≤
      ∑ b ∈ box Ps γ', e (smooth Ps b) * π b := by
    calc ∑ n ∈ D, nuD ν n / n * ((1 - ((p : ℝ)⁻¹) ^ J n) / ((p : ℝ) - 1))
        ≤ ∑ n ∈ D, e (smooth Ps (expo n)) * π (expo n) := by
          refine sum_le_sum fun n hn => ?_
          have hn0 := (hD n hn).1
          rw [hexpo n hn, hπ]
          simp only
          rw [prod_tailP_expo hPs hn0.ne' (hD n hn).2 ν, mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · simp only [he]
            have := wp_le_of_mul_pow_lt hp hn0 (hJ n hn)
            rw [sub_div]
            linarith
          · rw [← prod_tailP_expo hPs hn0.ne' (hD n hn).2 ν]
            exact hπ0 _
      _ = ∑ b ∈ D.image expo, e (smooth Ps b) * π b := by
          rw [sum_image]
          intro a ha b hb hab
          have := congrArg (smooth Ps) hab
          rwa [hexpo a ha, hexpo b hb] at this
      _ ≤ ∑ b ∈ box Ps γ', e (smooth Ps b) * π b := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => mul_nonneg (he0 _) (hπ0 b)
          intro b hb
          obtain ⟨n, hn, rfl⟩ := mem_image.1 hb
          refine expo_mem_box (hD n hn).1.ne' (hD n hn).2 fun q hq => ?_
          exact (le_sup (f := id) hn).trans (hγ' q hq)
  rw [hsplit]
  have h3 : 1 / ((p : ℝ) - 1) * ∑ b ∈ box Ps γ', π b ≤
      (∏ q ∈ Ps, (1 + ν q / ((q : ℝ) - 1))) / ((p : ℝ) - 1) := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right h1 hpm.le
  linarith

/-- **First moment, certificate form** (`δ p = 0`), with tilt upper bounds `ν`:
for every cap `γ`,
`hingeLoss m δ p γ ≤ (Π_{q<p} (1 + ν_q/(q-1)))/(p-1) - Σ_{n∈D} ν(n)/n · (1 - p^{-J n})/(p-1)`,
where `D` is any finite set of positive integers all of whose prime factors are `< p`, and
`n p^{J n} < m` whenever `J n ≠ 0`. -/
theorem hingeLoss_le_firstMoment {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hδp : δ p = 0)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (D : Finset ℕ)
    (hD : ∀ n ∈ D, 0 < n ∧ ∀ r ∈ n.primeFactors, r < p) (J : ℕ → ℕ)
    (hJ : ∀ n ∈ D, J n ≠ 0 → n * p ^ J n < m) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤
      (∏ q ∈ Nat.primesBelow p, (1 + ν q / ((q : ℝ) - 1))) / ((p : ℝ) - 1) -
        ∑ n ∈ D, nuD ν n / n * ((1 - ((p : ℝ)⁻¹) ^ J n) / ((p : ℝ) - 1)) := by
  have hmain := hingeLoss_le_of_tilt_le (m := m) hp.one_lt (by rw [hδp]; norm_num) hδ hν γ
  have hU : ∀ v, max 0 (Up p m (smooth (Nat.primesBelow p) v) - δ p) =
      Up p m (smooth (Nat.primesBelow p) v) := fun v => by
    rw [hδp, sub_zero, max_eq_right (Up_nonneg hp.one_lt m _)]
  simp_rw [hU, hδp, sub_zero, div_one] at hmain
  refine hmain.trans (expect_Up_le_firstMoment (fun q hq => Nat.prime_of_mem_primesBelow hq)
    (nu_mem_of_tilt_le hδ hν) hp.one_lt D (fun n hn => ⟨(hD n hn).1, fun r hr => ?_⟩) J hJ γ)
  exact Nat.mem_primesBelow.2 ⟨(hD n hn).2 r hr, Nat.prime_of_mem_primeFactors hr⟩

/-- **First moment when every `δ_q = 0` (`q ≤ p`)**, in the arithmetic form computed by
`CheckerImpl.firstMoment`: for every cap `γ`,
`hingeLoss m δ p γ ≤ (Π_{q<p} q)/((Π_{q<p} (q-1))(p-1)) - Σ_{n∈D} (p^{J n} - 1)/((p-1) p^{J n} n)`. -/
theorem hingeLoss_le_firstMoment_of_zero {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hδp : δ p = 0)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q = 0) (D : Finset ℕ)
    (hD : ∀ n ∈ D, 0 < n ∧ ∀ r ∈ n.primeFactors, r < p) (J : ℕ → ℕ)
    (hJ : ∀ n ∈ D, J n ≠ 0 → n * p ^ J n < m) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤
      (∏ q ∈ Nat.primesBelow p, (q : ℝ)) /
          ((∏ q ∈ Nat.primesBelow p, ((q : ℝ) - 1)) * ((p : ℝ) - 1)) -
        ∑ n ∈ D, ((p : ℝ) ^ J n - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ J n * n) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h := hingeLoss_le_firstMoment (m := m) hp hδp (fun q hq => by rw [hδ q hq]; norm_num)
    (ν := fun _ => 1) (fun q hq => ⟨by rw [tilt_eq_one_of_eq_zero (hδ q hq)],
      by exact_mod_cast (Nat.prime_of_mem_primesBelow hq).one_lt.le⟩) D hD J hJ γ
  refine h.trans (le_of_eq ?_)
  congr 1
  · have e : ∏ q ∈ Nat.primesBelow p, (1 + 1 / ((q : ℝ) - 1)) =
        (∏ q ∈ Nat.primesBelow p, (q : ℝ)) / ∏ q ∈ Nat.primesBelow p, ((q : ℝ) - 1) := by
      rw [← prod_div_distrib]
      refine prod_congr rfl fun q hq => ?_
      have hq1 : (1 : ℝ) < q := by exact_mod_cast (Nat.prime_of_mem_primesBelow hq).one_lt
      have hq0 : (q : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e, div_div]
  · refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hD n hn).1
    rw [nuD_one_eq, inv_pow]
    have hpJ : (0 : ℝ) < (p : ℝ) ^ J n := by positivity
    field_simp

end MinModulus.CheckerMath
