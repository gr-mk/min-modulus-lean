import MinModulus.CheckerSound.CompCostLoops

/-!
# `CheckerSound.CompCostRem` (agent CS-C): the remainder, tail and final division of
`comparisonCost`

Status: complete, no `sorry`.

* **`rem_part_le`**: with `R_k = up[k] - pen[k]` (truncated), the non-enumerated mass term
  `Σ_{k ≤ KMAX} R_k G(k/(p-1), k/(p-1)) ≤ pv remlin + pv remfb`, where `(rs0, rs1, remfb)` is the
  output of the `remaining` loop over `k ∈ [1, min KMAX kTop]` and
  `remlin = ⌈EB·rs1/((p-1) 2^62)⌉ - ⌊dn·rs0/10^9⌋`. (`k = 0` contributes `G(0,0) = 0`; `k > kTop`
  has `up[k] = 0`.) Linear `k` (`k/(p-1) ≥ t`) use `CheckerMath.GB_le_of_ge_bounds`, the others
  the diagonal `gUp` bound (hypothesis `hG`, CS-B's `BValid_gUp_diag_ge`).
* `pv_tail_ge`: `LA·EB/(p-1) ≤ pv ⌈tailA·EB/((p-1) 2^62)⌉`;
* `pv_cost_ge`: `pv total / (1 - dn/10^9) ≤ pv ⌈total·10^9/(10^9 - dn)⌉`.
-/

namespace MinModulus.CheckerSound.C

open MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Smooth Finset

theorem GB_zero_zero {S : Finset ℕ} {ν : ℕ → ℝ} (hνS : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ)
    {t : ℝ} (ht : 0 ≤ t) : GB S ν γ t 0 0 = 0 :=
  le_antisymm (by simpa using GB_diag_le hνS γ le_rfl ht (α := 0)) (GB_nonneg hνS γ t 0 0)

theorem pv_div_DDEN_le (x : ℕ) : pv (x / DDEN) ≤ pv x / 10 ^ 9 := by
  unfold pv
  rw [div_div, mul_comm, ← div_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have := cast_div_le x DDEN
  rwa [cast_DDEN] at this

theorem pv_mul_div_DDEN (dn x : ℕ) : pv (dn * x) / 10 ^ 9 = (dn : ℝ) / 10 ^ 9 * pv x := by
  rw [pv_mul_left]
  ring

/-- **The non-enumerated `τ_A`-mass** (`remaining`): see the module docstring. -/
theorem rem_part_le {S : Finset ℕ} {ν : ℕ → ℝ} (hνS : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q) {γ : ℕ → ℕ}
    {p dn KMAX kTop uDen : ℕ} (hp : 2 ≤ p) (up pen : Array ℕ)
    (htop : ∀ k, kTop < k → up[k]! = 0) {EB : ℕ} (hEB : meanTau S ν γ ≤ pv EB) {fb : ℕ → ℕ}
    (hG : ∀ k, 1 ≤ k → k * DDEN ≤ dn * (p - 1) →
      GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) ≤
        pv (gUp fb dn p k k (p - 1)))
    {rs0 rs1 remfb : ℕ}
    (hr : comparisonCost.remaining p dn fb uDen up pen 1 0 0 0 (min KMAX kTop) = (rs0, rs1, remfb)) :
    ∑ k ∈ range (KMAX + 1), pv (up[k]! - getD0 pen k) *
        GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) ≤
      pv (cdiv (EB * rs1) ((p - 1) * ONE) - dn * rs0 / DDEN) + pv remfb := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have ht0 : (0 : ℝ) ≤ (dn : ℝ) / 10 ^ 9 := by positivity
  rw [remaining_eq] at hr
  simp only [Prod.mk.injEq, Nat.zero_add] at hr
  obtain ⟨h0, h1, h2⟩ := hr
  -- only `k ∈ [1, min KMAX kTop]` contributes
  have hsub : ∑ k ∈ Ico 1 (1 + min KMAX kTop), pv (up[k]! - getD0 pen k) *
        GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) =
      ∑ k ∈ range (KMAX + 1), pv (up[k]! - getD0 pen k) *
        GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) := by
    refine sum_subset (fun k hk => ?_) (fun k hk hnk => ?_)
    · rw [mem_Ico] at hk; rw [mem_range]; omega
    · rw [mem_range] at hk
      rw [mem_Ico] at hnk
      by_cases hk0 : k = 0
      · subst hk0
        rw [Nat.cast_zero, zero_div, GB_zero_zero hνS γ ht0, mul_zero]
      · have hkt : kTop < k := by omega
        rw [htop k hkt, Nat.zero_sub, pv_zero, zero_mul]
  rw [← hsub]
  have hsplit : ∑ k ∈ Ico 1 (1 + min KMAX kTop), pv (up[k]! - getD0 pen k) *
        GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) =
      ∑ k ∈ Ico 1 (1 + min KMAX kTop), (if dn * (p - 1) ≤ k * DDEN then pv (up[k]! - getD0 pen k) *
        GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1)) else 0) +
      ∑ k ∈ Ico 1 (1 + min KMAX kTop), (if dn * (p - 1) ≤ k * DDEN then 0 else
        pv (up[k]! - getD0 pen k) *
          GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1))) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun k _ => by split_ifs <;> simp
  rw [hsplit]
  refine add_le_add ?_ ?_
  · -- linear `k`: `R_k G ≤ R_k (k·EB/(p-1) - t)`
    have hpt : ∀ k ∈ Ico 1 (1 + min KMAX kTop), (if dn * (p - 1) ≤ k * DDEN then
          pv (up[k]! - getD0 pen k) *
            GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1))
          else 0) ≤
        pv EB / ((p : ℝ) - 1) *
            pv (if dn * (p - 1) ≤ k * DDEN then k * (up[k]! - getD0 pen k) else 0) -
          (dn : ℝ) / 10 ^ 9 * pv (if dn * (p - 1) ≤ k * DDEN then up[k]! - getD0 pen k else 0) := by
      intro k _
      by_cases hl : dn * (p - 1) ≤ k * DDEN
      · rw [ite_eq_left hl, ite_eq_left hl, ite_eq_left hl, pv_mul_left]
        have htk : (dn : ℝ) / 10 ^ 9 ≤ (k : ℝ) / ((p : ℝ) - 1) := by
          have h' : ((dn * (p - 1) : ℕ) : ℝ) ≤ ((k * DDEN : ℕ) : ℝ) := by exact_mod_cast hl
          push_cast [Nat.cast_sub (show 1 ≤ p by omega)] at h'
          rw [cast_DDEN] at h'
          rw [div_le_div_iff₀ (by norm_num) hp1]
          linarith
        have hb := GB_le_of_ge_bounds hνS γ (le_refl ((k : ℝ) / ((p : ℝ) - 1)))
          (by positivity) le_rfl htk hEB
        have hR0 := pv_nonneg (up[k]! - getD0 pen k)
        calc pv (up[k]! - getD0 pen k) *
              GB S ν γ ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1)) ((k : ℝ) / ((p : ℝ) - 1))
            ≤ pv (up[k]! - getD0 pen k) * (((k : ℝ) / ((p : ℝ) - 1) - (dn : ℝ) / 10 ^ 9) +
              (pv EB - 1) * ((k : ℝ) / ((p : ℝ) - 1))) := mul_le_mul_of_nonneg_left hb hR0
          _ = pv EB / ((p : ℝ) - 1) * ((k : ℝ) * pv (up[k]! - getD0 pen k)) -
              (dn : ℝ) / 10 ^ 9 * pv (up[k]! - getD0 pen k) := by
            field_simp
            ring
      · rw [ite_eq_right hl, ite_eq_right hl, ite_eq_right hl, pv_zero]
        simp
    refine (sum_le_sum hpt).trans ?_
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, ← pv_sum, ← pv_sum, h0, h1]
    -- `remlin`
    refine le_trans ?_ (pv_sub_ge _ _)
    have hc := pv_cdiv_ge (a := EB * rs1) (show 0 < (p - 1) * ONE from
      Nat.mul_pos (by omega) (by unfold ONE; omega))
    have e1 : pv (EB * rs1) / (((p - 1) * ONE : ℕ) : ℝ) = pv EB / ((p : ℝ) - 1) * pv rs1 := by
      rw [Nat.cast_mul, cast_ONE, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
      unfold pv
      push_cast
      field_simp
    rw [e1] at hc
    have hd := pv_div_DDEN_le (dn * rs0)
    rw [pv_mul_div_DDEN] at hd
    linarith
  · -- FB `k`: `R_k G ≤ R_k gUp ≤ mulUp`
    rw [← h2, pv_sum]
    refine sum_le_sum fun k hk => ?_
    by_cases hl : dn * (p - 1) ≤ k * DDEN
    · rw [ite_eq_left hl, ite_eq_left hl, pv_zero]
    · rw [ite_eq_right hl, ite_eq_right hl]
      have hk1 : 1 ≤ k := (mem_Ico.1 hk).1
      have hkt : k * DDEN ≤ dn * (p - 1) := by omega
      exact (mul_le_mul_of_nonneg_left (hG k hk1 hkt) (pv_nonneg _)).trans (pv_mul_le_mulUp _ _)

/-- The lost `τ_A`-mass term. -/
theorem pv_tail_ge (tailA EB p : ℕ) (hp : 2 ≤ p) :
    pv tailA * pv EB / ((p : ℝ) - 1) ≤ pv (cdiv (tailA * EB) ((p - 1) * ONE)) := by
  refine le_trans (le_of_eq ?_) (pv_cdiv_ge (show 0 < (p - 1) * ONE from
    Nat.mul_pos (by omega) (by unfold ONE; omega)))
  rw [Nat.cast_mul, cast_ONE, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  unfold pv
  push_cast
  field_simp

/-- The final division by `1 - t`: `pv total / (1 - dn/10^9) ≤ pv ⌈total·10^9/(10^9 - dn)⌉`. -/
theorem pv_cost_ge (total dn : ℕ) (hdn : dn < DDEN) :
    pv total / (1 - (dn : ℝ) / 10 ^ 9) ≤ pv (cdiv (total * DDEN) (DDEN - dn)) := by
  have hd : (dn : ℝ) < 10 ^ 9 := by
    have : ((dn : ℕ) : ℝ) < ((DDEN : ℕ) : ℝ) := by exact_mod_cast hdn
    rwa [cast_DDEN] at this
  refine le_trans (le_of_eq ?_) (pv_cdiv_ge (Nat.sub_pos_of_lt hdn))
  rw [Nat.cast_sub hdn.le, cast_DDEN, mul_comm, pv_mul_left, cast_DDEN]
  have h1 : (0 : ℝ) < 10 ^ 9 - dn := by linarith
  field_simp

end MinModulus.CheckerSound.C
