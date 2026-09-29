import MinModulus.CheckerMath.GFun

/-!
# `CheckerMath`, part 3: the A/B split and the enumerated/remainder split

The primes below `p` are split into two disjoint sets `A` (small primes, enumerated) and `B`
(the rest, handled through the law of `τ_B`). The split is arbitrary: soundness does not depend
on how `A` is chosen (`rigcert.c` takes `A = {q ≤ z}`, `z` the largest prime `≤ Z0 = 47` that is
`< ⌈m/p⌉`).

## Results (for every cap `γ`)
* `expect_hinge_le_split` (**A/B split**, from `Smooth.expect_union`, `Smooth.Up_smooth_union_le`
  and hinge monotonicity):
  `E[(U_p(s) - t)^+] ≤ E_A[G(τ_A/(p-1), U_A(s_A))]`, `G = GB B ν γ t` (see `GFun.lean`).
* `expect_GB_le_enum` (**enumerated vs. remainder**): for any set `E` of `A`-configurations
  ("enumerated"),
  `E_A[G(τ_A/(p-1), U_A)] ≤ Σ_{a ∈ E} π(a) G(τ_A(a)/(p-1), U_A(a))
      + Σ_{k ≤ KM} R_k G(k/(p-1), k/(p-1)) + LA · EB/(p-1)`,
  where `R_k ≥ P(τ_A = k, kept, ∉ E)` (`restMass`), `LA ≥ E[τ_A; lost]` (`TauLaw.lostMass`,
  truncation `τ_A ≤ KM`, exponents `≤ acut`), `EB ≥ E[τ_B]`. For `a ∉ E` it uses
  `U_A(a) ≤ τ_A(a)/(p-1)`; lost configurations use `G(α, α) ≤ α E[τ_B]`.
* `restMass_eq`: if every enumerated configuration with `τ_A ≤ KM` is kept (exponents
  `≤ acut`), then `P(τ_A = k, kept, ∉ E) = P(τ_A = k, kept) - Σ_{a ∈ E, τ_A(a) = k} π(a)`
  (`enumMass`), i.e. the code's `R_k = P_up(τ_A = k) - P_enum_lo(τ_A = k)`.
* Enumeration by depth-first search (`enumSum`, the sum over `s · s(v) ≤ X`):
  `enumSum_insert` (one prime at a time), `enumSum_empty`, `enumSum_eq_zero` (`s > X`), and
  `sum_filter_smooth_le_eq_enumSum` (`E = {s(v) ≤ X}` is `enumSum … X 1`).
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth

variable {A B : Finset ℕ} {ν : ℕ → ℝ} {γ : ℕ → ℕ}

/-! ### The A/B split -/

/-- **A/B split**: `E_{A∪B}[(U_p(s) - t)^+] ≤ E_A[G(τ_A/(p-1), U_A(s_A))]` with
`G(α, u) = E_B[(u + (τ_B - 1) α - t)^+]`. -/
theorem expect_hinge_le_split {p : ℕ} (hp : 1 < p) (m : ℕ) (hAB : Disjoint A B)
    (hA : ∀ q ∈ A, q.Prime) (hB : ∀ q ∈ B, q.Prime) (hν : ∀ q ∈ A ∪ B, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (t : ℝ) :
    expect (A ∪ B) ν γ (fun v => max 0 (Up p m (smooth (A ∪ B) v) - t)) ≤
      expect A ν γ (fun a =>
        GB B ν γ t ((tauN A a : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth A a))) := by
  have hνA : ∀ q ∈ A, 0 ≤ ν q ∧ ν q ≤ q := fun q hq => hν q (mem_union_left B hq)
  have hνB : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q := fun q hq => hν q (mem_union_right A hq)
  rw [expect_union hAB]
  refine expect_mono hνA fun a ha => ?_
  unfold GB
  refine expect_mono hνB fun b hb => ?_
  have hsplit := Up_smooth_union_le hAB hA hB hp m (v := a) (w := b)
    (fun q hq => (mem_box.1 ha).2 q (disjoint_right.1 hAB hq))
    (fun q hq => (mem_box.1 hb).2 q (disjoint_left.1 hAB hq))
  rw [card_divisors_smooth_eq_tauN hA, card_divisors_smooth_eq_tauN hB] at hsplit
  refine max_le_max le_rfl ?_
  have e : ((tauN B b : ℝ) - 1) * (tauN A a : ℝ) / ((p : ℝ) - 1) =
      ((tauN B b : ℝ) - 1) * ((tauN A a : ℝ) / ((p : ℝ) - 1)) := by ring
  linarith

/-! ### Enumerated vs. remainder -/

/-- `P(τ_A = k ∧ kept ∧ ¬ E)`: the kept, non-enumerated mass at `τ_A = k`. -/
noncomputable def restMass (A : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (KM : ℕ) (acut : ℕ → ℕ)
    (E : (ℕ → ℕ) → Prop) [DecidablePred E] (k : ℕ) : ℝ :=
  expect A ν γ (fun a => if tauN A a = k ∧ Kept A KM acut a ∧ ¬ E a then 1 else 0)

/-- The enumerated mass at `τ_A = k`: `Σ_{a ∈ E, τ_A(a) = k} π(a)`. -/
noncomputable def enumMass (A : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (E : (ℕ → ℕ) → Prop)
    [DecidablePred E] (k : ℕ) : ℝ :=
  ∑ a ∈ (box A γ).filter E, weight A ν γ a * (if tauN A a = k then 1 else 0)

theorem restMass_nonneg (hν : ∀ q ∈ A, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (KM : ℕ)
    (acut : ℕ → ℕ) (E : (ℕ → ℕ) → Prop) [DecidablePred E] (k : ℕ) :
    0 ≤ restMass A ν γ KM acut E k :=
  expect_nonneg hν fun _ _ => by split_ifs <;> norm_num

/-- `R_k = P(τ_A = k, kept) - P(τ_A = k, enumerated)` when every enumerated configuration with
`τ_A ≤ KM` is kept. -/
theorem restMass_eq {KM : ℕ} {acut : ℕ → ℕ} {E : (ℕ → ℕ) → Prop} [DecidablePred E]
    (hE : ∀ a ∈ box A γ, E a → tauN A a ≤ KM → ∀ q ∈ A, a q ≤ acut q) {k : ℕ} (hk : k ≤ KM) :
    restMass A ν γ KM acut E k = lawKept A ν γ KM acut k - enumMass A ν γ E k := by
  have h1 : enumMass A ν γ E k =
      expect A ν γ (fun a => if E a then (if tauN A a = k then 1 else 0) else 0) := by
    unfold enumMass Smooth.expect
    rw [sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hEa : E a <;> by_cases hτ : tauN A a = k <;> simp [hEa, hτ]
  rw [h1]
  unfold restMass lawKept
  rw [← expect_sub]
  refine expect_congr_fun fun a ha => ?_
  by_cases hEa : E a
  · by_cases hτ : tauN A a = k
    · have hle : tauN A a ≤ KM := by rw [hτ]; exact hk
      have hK : Kept A KM acut a := ⟨hle, hE a ha hEa hle⟩
      simp [hEa, hτ, hK]
    · simp [hEa, hτ]
  · simp [hEa]

/-- **Enumerated vs. remainder.** For any set `E` of `A`-configurations,
`E_A[G(τ_A/(p-1), U_A)] ≤ Σ_{a ∈ E} π(a) G(τ_A(a)/(p-1), U_A(a))
   + Σ_{k ≤ KM} R_k G(k/(p-1), k/(p-1)) + LA · EB/(p-1)`,
with `R_k ≥ P(τ_A = k, kept, ∉ E)`, `LA ≥ E[τ_A; lost]`, `EB ≥ E[τ_B]`, `t ≥ 0`. -/
theorem expect_GB_le_enum {p : ℕ} (hp : 1 < p) (m : ℕ) (hA : ∀ q ∈ A, q.Prime)
    (hνA : ∀ q ∈ A, 0 ≤ ν q ∧ ν q ≤ q) (hνB : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ)
    {t : ℝ} (ht : 0 ≤ t) (E : (ℕ → ℕ) → Prop) [DecidablePred E] (KM : ℕ) (acut : ℕ → ℕ)
    (R : ℕ → ℝ) (hR : ∀ k ≤ KM, restMass A ν γ KM acut E k ≤ R k)
    (LA : ℝ) (hLA : lostMass A ν γ KM acut ≤ LA) (EB : ℝ) (hEB : meanTau B ν γ ≤ EB) :
    expect A ν γ (fun a =>
        GB B ν γ t ((tauN A a : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth A a))) ≤
      ∑ a ∈ (box A γ).filter E, weight A ν γ a *
          GB B ν γ t ((tauN A a : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth A a)) +
        ∑ k ∈ range (KM + 1),
          R k * GB B ν γ t ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) +
        LA * EB / ((p : ℝ) - 1) := by
  set F : (ℕ → ℕ) → ℝ :=
    fun a => GB B ν γ t ((tauN A a : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth A a)) with hF
  set Gd : ℕ → ℝ :=
    fun k => GB B ν γ t ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) with hGd
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp
    linarith
  have hMB := meanTau_nonneg hνB γ
  -- split off the enumerated configurations
  have hsplit : expect A ν γ F = ∑ a ∈ (box A γ).filter E, weight A ν γ a * F a +
      expect A ν γ (fun a => if E a then 0 else F a) := by
    unfold Smooth.expect
    rw [← sum_filter_add_sum_filter_not (box A γ) E, sum_filter (fun a => ¬ E a)]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    by_cases hEa : E a <;> simp [hEa]
  -- pointwise bound for the non-enumerated configurations
  have hpt : ∀ a ∈ box A γ, (if E a then 0 else F a) ≤
      ∑ k ∈ range (KM + 1),
        (if tauN A a = k ∧ Kept A KM acut a ∧ ¬ E a then (1 : ℝ) else 0) * Gd k +
      (if Kept A KM acut a then 0 else (tauN A a : ℝ)) * (meanTau B ν γ / ((p : ℝ) - 1)) := by
    intro a _
    have hlost0 : 0 ≤ (if Kept A KM acut a then 0 else (tauN A a : ℝ)) *
        (meanTau B ν γ / ((p : ℝ) - 1)) := by
      refine mul_nonneg ?_ (div_nonneg hMB hp1.le)
      split_ifs
      · exact le_rfl
      · exact tauN_real_nonneg A a
    by_cases hEa : E a
    · rw [ite_eq_left hEa]
      have : ∀ k ∈ range (KM + 1),
          (if tauN A a = k ∧ Kept A KM acut a ∧ ¬ E a then (1 : ℝ) else 0) * Gd k = 0 :=
        fun k _ => by simp [hEa]
      rw [sum_congr rfl this, sum_const_zero, zero_add]
      exact hlost0
    · rw [ite_eq_right hEa]
      have e : ∀ k ∈ range (KM + 1),
          (if tauN A a = k ∧ Kept A KM acut a ∧ ¬ E a then (1 : ℝ) else 0) * Gd k =
          (if tauN A a = k ∧ Kept A KM acut a then (1 : ℝ) else 0) * Gd k :=
        fun k _ => by simp [hEa]
      rw [sum_congr rfl e, sum_ind_kept_mul A KM acut a Gd]
      -- `F a ≤ Gd (τ_A a)` since `U_A ≤ τ_A/(p-1)`
      have hU : Up p m (smooth A a) ≤ (tauN A a : ℝ) / ((p : ℝ) - 1) := by
        have := Up_le_card_div hp m (smooth A a)
        rwa [card_divisors_smooth_eq_tauN hA] at this
      have hFG : F a ≤ Gd (tauN A a) := GB_mono hνB γ t le_rfl hU
      by_cases hK : Kept A KM acut a
      · rw [ite_eq_left hK, ite_eq_left hK, zero_mul, add_zero]
        exact hFG
      · rw [ite_eq_right hK, ite_eq_right hK, zero_add]
        have hd := GB_diag_le hνB γ (div_nonneg (tauN_real_nonneg A a) hp1.le) ht
          (t := t) (B := B)
        calc F a ≤ Gd (tauN A a) := hFG
          _ ≤ (tauN A a : ℝ) / ((p : ℝ) - 1) * meanTau B ν γ := hd
          _ = (tauN A a : ℝ) * (meanTau B ν γ / ((p : ℝ) - 1)) := by ring
  -- expectation of the pointwise bound
  have hexp : expect A ν γ (fun a =>
      ∑ k ∈ range (KM + 1),
        (if tauN A a = k ∧ Kept A KM acut a ∧ ¬ E a then (1 : ℝ) else 0) * Gd k +
      (if Kept A KM acut a then 0 else (tauN A a : ℝ)) * (meanTau B ν γ / ((p : ℝ) - 1))) =
      ∑ k ∈ range (KM + 1), restMass A ν γ KM acut E k * Gd k +
        lostMass A ν γ KM acut * (meanTau B ν γ / ((p : ℝ) - 1)) := by
    rw [expect_add, expect_sum, expect_mul_const]
    congr 1
    exact sum_congr rfl fun k _ => expect_mul_const _ _
  have hGd0 : ∀ k, 0 ≤ Gd k := fun k => GB_nonneg hνB γ t _ _
  have h1 : ∑ k ∈ range (KM + 1), restMass A ν γ KM acut E k * Gd k ≤
      ∑ k ∈ range (KM + 1), R k * Gd k :=
    sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
      (hR k (Nat.lt_succ_iff.1 (mem_range.1 hk))) (hGd0 k)
  have hLA0 : 0 ≤ LA := (lostMass_nonneg hνA γ KM acut).trans hLA
  have h2 : lostMass A ν γ KM acut * (meanTau B ν γ / ((p : ℝ) - 1)) ≤
      LA * EB / ((p : ℝ) - 1) := by
    rw [mul_div_assoc]
    exact mul_le_mul hLA (div_le_div_of_nonneg_right hEB hp1.le) (div_nonneg hMB hp1.le) hLA0
  have h3 := expect_mono hνA hpt
  rw [hexp] at h3
  rw [hsplit]
  linarith

/-! ### Enumeration by depth-first search -/

/-- The sum over the configurations `v` with `s · s(v) ≤ X` of `π(v) F(v)` (the depth-first
enumeration of `rigcert.c`'s `enumA`, started with `s = 1`). -/
noncomputable def enumSum (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (X s : ℕ)
    (F : (ℕ → ℕ) → ℝ) : ℝ :=
  ∑ v ∈ (box Ps γ).filter (fun v => s * smooth Ps v ≤ X), weight Ps ν γ v * F v

theorem enumSum_eq_expect (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (X s : ℕ)
    (F : (ℕ → ℕ) → ℝ) :
    enumSum Ps ν γ X s F = expect Ps ν γ (fun v => if s * smooth Ps v ≤ X then F v else 0) := by
  unfold enumSum Smooth.expect
  rw [sum_filter]
  refine sum_congr rfl fun v _ => ?_
  by_cases h : s * smooth Ps v ≤ X <;> simp [h]

theorem enumSum_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (X s : ℕ) (F : (ℕ → ℕ) → ℝ) :
    enumSum ∅ ν γ X s F = if s ≤ X then F 0 else 0 := by
  rw [enumSum_eq_expect, expect_empty]
  simp

/-- **One step of the depth-first enumeration**: for `q ∉ Ps`,
`enumSum (insert q Ps) X s F = Σ_{a ≤ γ q} ρ_q(a) · enumSum Ps X (s q^a) (F ∘ update · q a)`.
(Terms with `s q^a > X` vanish, `enumSum_eq_zero`.) -/
theorem enumSum_insert {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ)
    (X s : ℕ) (F : (ℕ → ℕ) → ℝ) :
    enumSum (insert q Ps) ν γ X s F =
      ∑ a ∈ range (γ q + 1), rho q (ν q) (γ q) a *
        enumSum Ps ν γ X (s * q ^ a) (fun w => F (Function.update w q a)) := by
  rw [enumSum_eq_expect, expect_insert hq]
  refine sum_congr rfl fun a _ => ?_
  rw [enumSum_eq_expect]
  congr 1
  refine expect_congr_fun fun w _ => ?_
  rw [smooth_insert hq, Function.update_self, smooth_update_of_notMem hq, mul_assoc]

/-- A branch whose running product already exceeds `X` contributes nothing. -/
theorem enumSum_eq_zero {Ps : Finset ℕ} (hPs : ∀ q ∈ Ps, 0 < q) (ν : ℕ → ℝ) (γ : ℕ → ℕ)
    {X s : ℕ} (h : X < s) (F : (ℕ → ℕ) → ℝ) : enumSum Ps ν γ X s F = 0 := by
  unfold enumSum
  rw [filter_false_of_mem fun v _ => ?_, sum_empty]
  have : 1 ≤ smooth Ps v := smooth_pos hPs v
  have : s ≤ s * smooth Ps v := Nat.le_mul_of_pos_right s this
  omega

/-- The enumerated set `E = {v : s(v) ≤ X}` of `rigcert.c`: the sum over `E` is
`enumSum … X 1`. -/
theorem sum_filter_smooth_le_eq_enumSum (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (X : ℕ)
    (F : (ℕ → ℕ) → ℝ) :
    ∑ v ∈ (box Ps γ).filter (fun v => smooth Ps v ≤ X), weight Ps ν γ v * F v =
      enumSum Ps ν γ X 1 F := by
  unfold enumSum
  simp only [one_mul]

end MinModulus.CheckerMath
