import MinModulus.CheckerSound.EnumPat
import Mathlib.Algebra.BigOperators.Field

/-!
# `CheckerSound.CompCostLoops` (agent CS-C): the small loops of `comparisonCost`

Status: complete, no `sorry`.

* `arrSum_eq`, `weightedSum_eq`: `Σ a[i]`, `Σ i·a[i]` over the array;
* `fbLeaves_eq`: `fbLeaves … = acc + Σ_j mulUp fb[j] (gKey j)` (`gKey`: `gUp` at the decoded key);
* `remaining_eq`: the three sums of the `remaining` loop (linear / FB split of `R_k`);
* `sum_getD0_mul`: an array whose entries are the sums `Σ_{w ∈ S, P w, f w = j} g w` has
  `Σ_j arr[j]·h(j) = Σ_{w ∈ S, P w} g w · h (f w)` (aggregation by keys);
* `thresholds_spec`: `1 ≤ M2 ≤ M1`, `pj1 > 0`, and **`I/(pj1 (p-1)) = U_p(s)`** for the code's
  thresholds (`J ≤ 3`), via `CheckerMath.Up_eq_sigma`;
* `key_decode`: the index `((n1·M1 + σ1)·M2 + σ2)` decodes back to `(n1, σ1, σ2)`;
* real-number rounding helpers (`pv_sub_le`, `pv_cdiv_ge`, …).
-/

namespace MinModulus.CheckerSound.C

open MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Smooth Finset

/-! ### Rounding helpers in `ℝ` (P-values) -/

theorem pv_sub_ge (a b : ℕ) : pv a - pv b ≤ pv (a - b) := by
  unfold pv
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (cast_sub_ge a b) (by positivity)

theorem pv_sum {α : Type*} (S : Finset α) (f : α → ℕ) : pv (∑ x ∈ S, f x) = ∑ x ∈ S, pv (f x) := by
  unfold pv
  push_cast
  rw [sum_div]

theorem pv_mul_left (a b : ℕ) : pv (a * b) = (a : ℝ) * pv b := by
  unfold pv
  push_cast
  ring

/-- `⌈a/b⌉` as a P-value is at least `pv a / b`. -/
theorem pv_cdiv_ge {a b : ℕ} (hb : 0 < b) : pv a / b ≤ pv (cdiv a b) := by
  unfold pv
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right (cdiv_ge hb) (by positivity)

theorem mulUp_zero_left (y : ℕ) : mulUp 0 y = 0 := by
  unfold mulUp
  rw [Nat.zero_mul, Nat.zero_add]
  exact Nat.div_eq_of_lt (by unfold ONE; omega)

/-! ### `arrSum`, `weightedSum` -/

theorem foldl_add_eq (l : List ℕ) (c : ℕ) :
    l.foldl (· + ·) c = c + ∑ i ∈ range l.length, l.getD i 0 := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem arrSum_eq (a : Array ℕ) : arrSum a = ∑ j ∈ range a.size, getD0 a j := by
  unfold arrSum
  rw [← Array.foldl_toList, foldl_add_eq, Nat.zero_add, Array.length_toList]
  refine sum_congr rfl fun j _ => ?_
  rw [getD0_eq, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem weightedSum_go_eq (a : Array ℕ) : ∀ f i acc,
    weightedSum.go a i acc f = acc + ∑ j ∈ Ico i (i + f), j * getD0 a j := by
  intro f
  induction f with
  | zero => intro i acc; simp [weightedSum.go]
  | succ f ih =>
    intro i acc
    rw [weightedSum.go, ih, sum_eq_sum_Ico_succ_bot (show i < i + (f + 1) by omega),
      show i + (f + 1) = i + 1 + f by omega, getD0_eq_getElem!]
    ring

theorem weightedSum_eq (a : Array ℕ) : weightedSum a = ∑ j ∈ range a.size, j * getD0 a j := by
  unfold weightedSum
  rw [weightedSum_go_eq, Nat.zero_add, Nat.zero_add, range_eq_Ico]

/-! ### `fbLeaves`, `remaining` -/

/-- `gUp` at the decoded key `j = (n1·M1 + σ1)·M2 + σ2` (as in `fbLeaves`). -/
def gKey (cfg : EnumCfg) (fb : ℕ → ℕ) (dn p uDen j : ℕ) : ℕ :=
  gUp fb dn p (j / (cfg.M2 * cfg.M1) + (j / cfg.M2) % cfg.M1)
    (cfg.pj1 * (j / (cfg.M2 * cfg.M1)) + cfg.pj2 * ((j / cfg.M2) % cfg.M1 - j % cfg.M2) +
      j % cfg.M2) uDen

theorem fbLeaves_eq (p dn : ℕ) (fb : ℕ → ℕ) (cfg : EnumCfg) (uDen : ℕ) (fbArr : Array ℕ) :
    ∀ f idx acc, comparisonCost.fbLeaves p dn fb cfg uDen fbArr idx acc f =
      acc + ∑ j ∈ Ico idx (idx + f), mulUp (getD0 fbArr j) (gKey cfg fb dn p uDen j) := by
  intro f
  induction f with
  | zero => intro idx acc; simp [comparisonCost.fbLeaves]
  | succ f ih =>
    intro idx acc
    rw [comparisonCost.fbLeaves, sum_eq_sum_Ico_succ_bot (show idx < idx + (f + 1) by omega),
      show idx + (f + 1) = idx + 1 + f by omega]
    by_cases h0 : fbArr[idx]! = 0
    · have hc : (fbArr[idx]! == 0) = true := by simp [h0]
      rw [ite_eq_left hc, ih, getD0_eq_getElem!, h0, mulUp_zero_left, Nat.zero_add]
    · have hc : ¬ (fbArr[idx]! == 0) = true := by simp [h0]
      rw [ite_eq_right hc]
      simp only
      rw [ih, Nat.add_assoc, getD0_eq_getElem!]
      rfl

theorem remaining_eq (p dn : ℕ) (fb : ℕ → ℕ) (uDen : ℕ) (up pen : Array ℕ) :
    ∀ f k rs0 rs1 remfb, comparisonCost.remaining p dn fb uDen up pen k rs0 rs1 remfb f =
      (rs0 + ∑ j ∈ Ico k (k + f), (if dn * (p - 1) ≤ j * DDEN then up[j]! - getD0 pen j else 0),
       rs1 + ∑ j ∈ Ico k (k + f),
          (if dn * (p - 1) ≤ j * DDEN then j * (up[j]! - getD0 pen j) else 0),
       remfb + ∑ j ∈ Ico k (k + f), (if dn * (p - 1) ≤ j * DDEN then 0
          else mulUp (up[j]! - getD0 pen j) (gUp fb dn p j j (p - 1)))) := by
  intro f
  induction f with
  | zero => intro k rs0 rs1 remfb; simp [comparisonCost.remaining]
  | succ f ih =>
    intro k rs0 rs1 remfb
    rw [comparisonCost.remaining, sum_eq_sum_Ico_succ_bot (show k < k + (f + 1) by omega),
      sum_eq_sum_Ico_succ_bot (show k < k + (f + 1) by omega),
      sum_eq_sum_Ico_succ_bot (show k < k + (f + 1) by omega),
      show k + (f + 1) = k + 1 + f by omega]
    by_cases h0 : up[k]! - getD0 pen k = 0
    · have hc : (up[k]! - getD0 pen k == 0) = true := by simp [h0]
      rw [ite_eq_left hc, ih, h0]
      simp only [Nat.mul_zero, mulUp_zero_left, ite_self, Nat.zero_add]
    · have hc : ¬ (up[k]! - getD0 pen k == 0) = true := by simp [h0]
      rw [ite_eq_right hc]
      by_cases hl : dn * (p - 1) ≤ k * DDEN
      · rw [ite_eq_left hl, ih, ite_eq_left hl, ite_eq_left hl, ite_eq_left hl]
        simp only [Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring⟩
      · rw [ite_eq_right hl, ih, ite_eq_right hl, ite_eq_right hl, ite_eq_right hl]
        simp only [Prod.mk.injEq]
        refine ⟨by ring, by ring, by ring⟩

/-! ### Aggregation by keys -/

/-- An array whose entries are `arr[j] = Σ_{w ∈ S, P w, f w = j} g w` satisfies
`Σ_{j < size} arr[j]·h(j) = Σ_{w ∈ S, P w} g w · h (f w)`: nothing is lost beyond the size
(those entries are `0`, hence so are their summands). -/
theorem sum_getD0_mul {α : Type*} (arr : Array ℕ) (S : Finset α) (P : α → Prop)
    [DecidablePred P] (f g : α → ℕ)
    (hv : ∀ j, getD0 arr j = ∑ w ∈ S, if P w ∧ j = f w then g w else 0) (h : ℕ → ℕ) :
    ∑ j ∈ range arr.size, getD0 arr j * h j = ∑ w ∈ S.filter P, g w * h (f w) := by
  have e1 : ∀ j, getD0 arr j * h j = ∑ w ∈ S, if P w ∧ j = f w then g w * h j else 0 := by
    intro j
    rw [hv j, sum_mul]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp_rw [e1]
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun w hw => ?_
  have e2 : ∑ j ∈ range arr.size, (if P w ∧ j = f w then g w * h j else 0) =
      if P w ∧ f w < arr.size then g w * h (f w) else 0 := by
    by_cases hP : P w
    · simp only [hP, true_and]
      rw [sum_ite_eq' (range arr.size) (f w) (fun j => g w * h j)]
      simp [mem_range]
    · simp [hP]
  rw [e2]
  by_cases hP : P w
  · by_cases hlt : f w < arr.size
    · rw [ite_eq_left ⟨hP, hlt⟩, ite_eq_left hP]
    · rw [ite_eq_right (fun hc => hlt hc.2), ite_eq_left hP]
      have h0 : g w = 0 := by
        have hz := hv (f w)
        rw [getD0_of_size_le (Nat.le_of_not_lt hlt)] at hz
        have := single_le_sum (f := fun w' => if P w' ∧ f w = f w' then g w' else 0)
          (fun _ _ => Nat.zero_le _) hw
        simp only [hP, true_and, ite_true] at this
        omega
      rw [h0, Nat.zero_mul]
  · rw [ite_eq_right (fun hc => hP hc.1), ite_eq_right hP]

/-! ### The thresholds -/

/-- `σ_M(s) = #{d ∣ s : d < M}`. -/
def sig (M s : ℕ) : ℕ := (s.divisors.filter (· < M)).card

theorem sig_le_card (M s : ℕ) : sig M s ≤ s.divisors.card :=
  card_le_card (filter_subset _ _)

theorem sig_mono {M M' : ℕ} (h : M ≤ M') (s : ℕ) : sig M s ≤ sig M' s :=
  card_le_card fun x hx => by
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

theorem sig_lt {M : ℕ} (hM : 1 ≤ M) (s : ℕ) : sig M s < M := by
  have hsub : s.divisors.filter (· < M) ⊆ Ico 1 M := by
    intro d hd
    rw [mem_filter, Nat.mem_divisors] at hd
    rw [mem_Ico]
    refine ⟨Nat.pos_of_ne_zero ?_, hd.2⟩
    rintro rfl
    exact hd.1.2 (Nat.eq_zero_of_zero_dvd hd.1.1)
  have := card_le_card hsub
  rw [Nat.card_Ico] at this
  unfold sig
  omega

theorem sig_one (s : ℕ) : sig 1 s = 0 := by
  have := sig_lt (le_refl 1) s
  omega

/-- `m ≤ d·p` for every divisor when `⌈m/p⌉ ≤ 1`: every weight is `1/(p-1)`. -/
theorem Up_of_cdiv_le_one {p m : ℕ} (hp : 2 ≤ p) (h : cdiv m p ≤ 1) (s : ℕ) :
    Up p m s = (s.divisors.card : ℝ) / ((p : ℝ) - 1) := by
  have hmp : m ≤ p := by
    have := (cdiv_le_iff_le_mul (m := m) (d := 1) (by omega : 0 < p)).1 (by unfold cdiv at h; exact h)
    omega
  unfold Up
  have hw : ∀ d ∈ s.divisors, wp p m d = 1 / ((p : ℝ) - 1) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hj : j0 p m d = 1 :=
      j0_eq_of (by omega) hd0 le_rfl (by rw [pow_one]; exact hmp.trans (Nat.le_mul_of_pos_left p hd0))
        (Or.inl rfl)
    unfold wp
    rw [hj]
    simp
  rw [sum_congr rfl hw, sum_const, nsmul_eq_mul]
  ring

/-- **The code's thresholds** (`J ≤ 3`): `1 ≤ M2 ≤ M1`, `pj1 > 0`, and
`U_p(s) = (pj1 (τ - σ₁) + pj2 (σ₁ - σ₂) + σ₂) / (pj1 (p-1))`. -/
theorem thresholds_spec {m p J M1 M2 pj1 pj2 : ℕ} (hp : 2 ≤ p)
    (hth : thresholds m p = (J, M1, M2, pj1, pj2)) (hJ : J ≤ 3) :
    1 ≤ M2 ∧ M2 ≤ M1 ∧ 0 < pj1 ∧
    ∀ s : ℕ, ((pj1 * (s.divisors.card - sig M1 s) + pj2 * (sig M1 s - sig M2 s) + sig M2 s : ℕ) : ℝ) /
      ((pj1 * (p - 1) : ℕ) : ℝ) = Up p m s := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hcast1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hcdiv : ∀ {a b d : ℕ}, 0 < b → (cdiv a b ≤ d ↔ a ≤ d * b) := fun hb => by
    unfold cdiv; exact cdiv_le_iff_le_mul hb
  unfold thresholds at hth
  simp only at hth
  split_ifs at hth with h1 h2 h3
  · -- `J = 1`
    simp only [Prod.mk.injEq] at hth
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hth
    refine ⟨le_rfl, le_rfl, Nat.one_pos, fun s => ?_⟩
    rw [sig_one, Up_of_cdiv_le_one hp h1]
    push_cast [Nat.sub_zero, hcast1]
    ring
  · -- `J = 2`
    simp only [Prod.mk.injEq] at hth
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hth
    have hm2 : m ≤ p * p := by have := (hcdiv (by positivity)).1 h2; omega
    have hm1 : p < m := by
      by_contra hc
      exact h1 ((hcdiv (by omega)).2 (by omega))
    refine ⟨le_rfl, by omega, by omega, fun s => ?_⟩
    have hU := Up_eq_sigma (s := s) (by omega : 1 < p) (show m ≤ p ^ 3 by nlinarith)
      (M1 := cdiv m p) (M2 := 1) (fun d => hcdiv (by omega))
      (fun d => by
        constructor
        · intro hd; nlinarith
        · intro hd
          by_contra hc
          have : d = 0 := by omega
          subst this
          omega)
    rw [hU]
    have h2' := sig_le_card (cdiv m p) s
    change _ = ((p : ℝ) ^ 2 * ((s.divisors.card : ℝ) - (sig (cdiv m p) s : ℝ)) +
      (p : ℝ) * ((sig (cdiv m p) s : ℝ) - (sig 1 s : ℝ)) + (sig 1 s : ℝ)) /
        ((p : ℝ) ^ 2 * ((p : ℝ) - 1))
    rw [sig_one]
    push_cast [Nat.cast_sub h2', hcast1, Nat.sub_zero]
    field_simp
    ring
  · -- `J = 3`
    simp only [Prod.mk.injEq] at hth
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hth
    have hm3 : m ≤ p * p * p := by have := (hcdiv (by positivity)).1 h3; omega
    have hM21 : cdiv m (p * p) ≤ cdiv m p := by
      rw [hcdiv (by positivity)]
      have := (hcdiv (a := m) (b := p) (d := cdiv m p) (by omega)).1 le_rfl
      nlinarith
    refine ⟨by omega, hM21, by positivity, fun s => ?_⟩
    have hU := Up_eq_sigma (s := s) (by omega : 1 < p) (show m ≤ p ^ 3 by rw [pow_three]; linarith)
      (M1 := cdiv m p) (M2 := cdiv m (p * p)) (fun d => hcdiv (by omega))
      (fun d => by rw [sq]; exact hcdiv (by positivity))
    rw [hU]
    have h2' := sig_le_card (cdiv m p) s
    have h3' := sig_mono hM21 s
    change _ = ((p : ℝ) ^ 2 * ((s.divisors.card : ℝ) - (sig (cdiv m p) s : ℝ)) +
      (p : ℝ) * ((sig (cdiv m p) s : ℝ) - (sig (cdiv m (p * p)) s : ℝ)) +
        (sig (cdiv m (p * p)) s : ℝ)) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1))
    push_cast [Nat.cast_sub h2', Nat.cast_sub h3', hcast1]
    ring
  · -- `J = 4` is excluded
    simp only [Prod.mk.injEq] at hth
    omega

/-- The key `((n1·M1 + σ1)·M2 + σ2)` decodes back (`σ1 < M1`, `σ2 < M2`). -/
theorem key_decode {n1 σ1 σ2 M1 M2 : ℕ} (h1 : σ1 < M1) (h2 : σ2 < M2) :
    ((n1 * M1 + σ1) * M2 + σ2) % M2 = σ2 ∧
    (((n1 * M1 + σ1) * M2 + σ2) / M2) % M1 = σ1 ∧
    ((n1 * M1 + σ1) * M2 + σ2) / (M2 * M1) = n1 := by
  have hM2 : 0 < M2 := by omega
  have hM1 : 0 < M1 := by omega
  have hdiv : ((n1 * M1 + σ1) * M2 + σ2) / M2 = n1 * M1 + σ1 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM2, Nat.div_eq_of_lt h2, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  · rw [hdiv, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  · rw [← Nat.div_div_eq_div_mul, hdiv, Nat.add_comm, Nat.add_mul_div_right _ _ hM1,
      Nat.div_eq_of_lt h1, Nat.zero_add]

end MinModulus.CheckerSound.C
