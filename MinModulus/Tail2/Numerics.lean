import MinModulus.Tail2.Bound
import Mathlib.Tactic.IntervalCases

/-!
# Tail2.Numerics: the constants of the sharper tail at `X ≥ 2·10^8`, `X ≥ 10^9`, `X ≥ 2·10^9`

STATUS: complete, no `sorry` (L2-T). **Generated** by `SCRATCH/agents/lean2/tail2/gen_lean.py`
(exact rational arithmetic, mirrored by `norm_num` here). Every numeric fact is proved by
`norm_num`/`Real.exp_bound'`/`Real.abs_log_sub_add_sum_range_le`; no `decide`, no `native_decide`.

* `log43_le`: `log(4/3) ≤ 0.28768207246` (log series, 20 terms).
* `log_ge_2e8`, `log_ge_1e9`, `log_ge_2e9`: `19.11 ≤ log X` for `X ≥ 2·10^8`, `20.72 ≤ log X` for
  `X ≥ 10^9`, `21.41 ≤ log X` for `X ≥ 2·10^9`
  (`exp 1 < 2.7182818286` and `Real.exp_bound'`).
* `U2e8`, `U1e9`, `U2e9`: the 31 grid values `U k ≥ exp(EE·KK/L)(1 + k log 2/L)^a` (rounded up to 12 digits),
  checked step by step (`hstep_2e8`, `hstep_1e9`).
* `tail2_2e8`: `Σ_{p∈S} ∏_{q∈S,q<p}(1+g q)/(p−1)^2 ≤ 0.14102/X` for `X ≥ 2·10^8`;
  `tail2_1e9`: `≤ 0.12473/X` for `X ≥ 10^9`; `tail2_2e9`: `≤ 0.11882/X` for `X ≥ 2·10^9`.
-/

namespace MinModulus.Tail2

open Finset Real

theorem log43_le : Real.log (4 / 3) ≤ 0.28768207246 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 4) (by norm_num) 20
  have e : Real.log (1 - 1 / 4) = -Real.log (4 / 3) := by
    rw [show (1 : ℝ) - 1 / 4 = (4 / 3)⁻¹ by norm_num, Real.log_inv]
  rw [e] at h
  have h2 := (abs_le.1 h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  norm_num at h2 ⊢
  linarith

theorem EE_le : EE ≤ 0.28768207246 := log43_le

theorem exp_one_pow_le (n : ℕ) : Real.exp n ≤ 2.7182818286 ^ n := by
  rw [show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n

theorem exp_frac_2e8 : Real.exp 0.11 ≤ 1.1162780705 := by
  refine (Real.exp_bound' (x := 0.11) (by norm_num) (by norm_num) (n := 8) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem log_ge_2e8 {X : ℕ} (hX : 2 * 10 ^ 8 ≤ X) : (19.11 : ℝ) ≤ Real.log X := by
  have hX' : ((2 * 10 ^ 8 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
  have hpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX'
  rw [Real.le_log_iff_exp_le hpos]
  have e : (19.11 : ℝ) = ((19 : ℕ) : ℝ) + 0.11 := by norm_num
  rw [e, Real.exp_add]
  have h1 := exp_one_pow_le 19
  have h2 := exp_frac_2e8
  calc Real.exp ((19 : ℕ) : ℝ) * Real.exp 0.11 ≤ 2.7182818286 ^ 19 * 1.1162780705 :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ ≤ ((2 * 10 ^ 8 : ℕ) : ℝ) := by norm_num
    _ ≤ X := hX'

theorem exp_frac_1e9 : Real.exp 0.72 ≤ 2.0544332803 := by
  refine (Real.exp_bound' (x := 0.72) (by norm_num) (by norm_num) (n := 8) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem log_ge_1e9 {X : ℕ} (hX : 10 ^ 9 ≤ X) : (20.72 : ℝ) ≤ Real.log X := by
  have hX' : ((10 ^ 9 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
  have hpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX'
  rw [Real.le_log_iff_exp_le hpos]
  have e : (20.72 : ℝ) = ((20 : ℕ) : ℝ) + 0.72 := by norm_num
  rw [e, Real.exp_add]
  have h1 := exp_one_pow_le 20
  have h2 := exp_frac_1e9
  calc Real.exp ((20 : ℕ) : ℝ) * Real.exp 0.72 ≤ 2.7182818286 ^ 20 * 2.0544332803 :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ ≤ ((10 ^ 9 : ℕ) : ℝ) := by norm_num
    _ ≤ X := hX'

theorem exp_frac_2e9 : Real.exp 0.41 ≤ 1.5068177867 := by
  refine (Real.exp_bound' (x := 0.41) (by norm_num) (by norm_num) (n := 8) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem log_ge_2e9 {X : ℕ} (hX : 2 * 10 ^ 9 ≤ X) : (21.41 : ℝ) ≤ Real.log X := by
  have hX' : ((2 * 10 ^ 9 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
  have hpos : (0 : ℝ) < X := lt_of_lt_of_le (by norm_num) hX'
  rw [Real.le_log_iff_exp_le hpos]
  have e : (21.41 : ℝ) = ((21 : ℕ) : ℝ) + 0.41 := by norm_num
  rw [e, Real.exp_add]
  have h1 := exp_one_pow_le 21
  have h2 := exp_frac_2e9
  calc Real.exp ((21 : ℕ) : ℝ) * Real.exp 0.41 ≤ 2.7182818286 ^ 21 * 1.5068177867 :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ ≤ ((2 * 10 ^ 9 : ℕ) : ℝ) := by norm_num
    _ ≤ X := hX'

/-- Grid values for `L₀ = 19.11` (`X ≥ 2 * 10 ^ 8`), rounded up to 12 digits. -/
noncomputable def U2e8 : ℕ → ℝ
  | 0 => 1.094528909017
  | 1 => 1.472287557811
  | 2 => 1.960314020763
  | 3 => 2.585361454518
  | 4 => 3.379449988136
  | 5 => 4.380679400660
  | 6 => 5.634134912654
  | 7 => 7.192893302235
  | 8 => 9.119136863572
  | 9 => 11.485383036330
  | 10 => 14.375837848064
  | 11 => 17.887881627995
  | 12 => 22.133695769961
  | 13 => 27.242039644484
  | 14 => 33.360187084833
  | 15 => 40.656032199633
  | 16 => 49.320374594912
  | 17 => 59.569394421446
  | 18 => 71.647327998828
  | 19 => 85.829355105799
  | 20 => 102.424709366982
  | 21 => 121.780023509251
  | 22 => 144.282921606469
  | 23 => 170.365870779231
  | 24 => 200.510305166508
  | 25 => 235.251035338678
  | 26 => 275.180956676288
  | 27 => 320.956070596051
  | 28 => 373.300832864927
  | 29 => 433.013843604717
  | 30 => 500.973893953336
  | _ => 0

theorem U0_2e8 : Real.exp (EE * KK / 19.11) ≤ U2e8 0 := by
  have hy : EE * KK / 19.11 ≤ 0.28768207246 * (6 * (1 + 1 / 10 ^ 7)) / 19.11 := by
    unfold KK
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right EE_le (by norm_num)
  refine (Real.exp_le_exp.2 hy).trans ?_
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 10) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, U2e8]
  norm_num

theorem hstep_2e8 : ∀ k < 30, U2e8 k * (1 + xh 19.11 k) ^ 8 * (1 + rr * xh 19.11 k) ≤ U2e8 (k + 1) := by
  intro k hk
  interval_cases k <;> norm_num [U2e8, xh, l2hi, l2lo, rr]

theorem mono_2e8 : ∀ k < 30, U2e8 k ≤ U2e8 (k + 1) := by
  intro k hk
  interval_cases k <;> norm_num [U2e8]

/-- The constant at `L₀ = 19.11`: `≤ 0.14102` (exact value `0.141019425`). -/
theorem const_2e8 : dW / 6 * ((U2e8 0 - 1) + ∑ k ∈ range 30, (U2e8 (k + 1) - U2e8 k) / (Real.log 2 * 2 ^ (k + 1))) +
    100 / 189 * U2e8 30 / 2 ^ 30 ≤ 7051 / 50000 := by
  have hl2 := Real.log_two_gt_d9
  have hsum : ∑ k ∈ range 30, (U2e8 (k + 1) - U2e8 k) / (Real.log 2 * 2 ^ (k + 1)) ≤
      ∑ k ∈ range 30, (U2e8 (k + 1) - U2e8 k) / (0.6931471803 * 2 ^ (k + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    apply div_le_div_of_nonneg_left (sub_nonneg.2 (mono_2e8 k (mem_range.1 hk))) (by positivity)
    exact mul_le_mul_of_nonneg_right hl2.le (by positivity)
  have hval : dW / 6 * ((U2e8 0 - 1) + ∑ k ∈ range 30, (U2e8 (k + 1) - U2e8 k) / (0.6931471803 * 2 ^ (k + 1))) +
      100 / 189 * U2e8 30 / 2 ^ 30 ≤ 7051 / 50000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, U2e8, dW]
    norm_num
  have hd : 0 ≤ dW / 6 := by unfold dW; positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hd]

/-- **Sharper tail at `X ≥ 2 * 10 ^ 8`**: `Σ_{p∈S} ∏_{q∈S,q<p}(1+g q)/(p−1)^2 ≤ 0.14102/X`. -/
theorem tail2_2e8 {X : ℕ} (hX : 2 * 10 ^ 8 ≤ X) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ X < p) :
    ∑ p ∈ S, (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤
      7051 / 50000 / (X : ℝ) := by
  have hX8 : 10 ^ 8 ≤ X := le_trans (by norm_num) hX
  refine (tail2_generic hX8 (L₀ := 19.11) (by norm_num) (log_ge_2e8 hX) U2e8 30 (by norm_num) U0_2e8
    hstep_2e8 S hS).trans ?_
  exact div_le_div_of_nonneg_right (const_2e8) (Nat.cast_nonneg _)

/-- Grid values for `L₀ = 20.72` (`X ≥ 10 ^ 9`), rounded up to 12 digits. -/
noncomputable def U1e9 : ℕ → ℝ
  | 0 => 1.086873936649
  | 1 => 1.429215307951
  | 2 => 1.863055563327
  | 3 => 2.408783659574
  | 4 => 3.090485782983
  | 5 => 3.936472204855
  | 6 => 4.979860027263
  | 7 => 6.259215835667
  | 8 => 7.819262434292
  | 9 => 9.711654000945
  | 10 => 11.995824160179
  | 11 => 14.739911637354
  | 12 => 18.021768321199
  | 13 => 21.930054728888
  | 14 => 26.565428035416
  | 15 => 32.041827998163
  | 16 => 38.487866277910
  | 17 => 46.048324829279
  | 18 => 54.885769206487
  | 19 => 65.182282804513
  | 20 => 77.141328231162
  | 21 => 90.989742182158
  | 22 => 106.979870369177
  | 23 => 125.391849229721
  | 24 => 146.536041327869
  | 25 => 170.755631536214
  | 26 => 198.429391271682
  | 27 => 229.974618241460
  | 28 => 265.850259339846
  | 29 => 306.560224522524
  | 30 => 352.656899671535
  | _ => 0

theorem U0_1e9 : Real.exp (EE * KK / 20.72) ≤ U1e9 0 := by
  have hy : EE * KK / 20.72 ≤ 0.28768207246 * (6 * (1 + 1 / 10 ^ 7)) / 20.72 := by
    unfold KK
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right EE_le (by norm_num)
  refine (Real.exp_le_exp.2 hy).trans ?_
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 10) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, U1e9]
  norm_num

theorem hstep_1e9 : ∀ k < 30, U1e9 k * (1 + xh 20.72 k) ^ 8 * (1 + rr * xh 20.72 k) ≤ U1e9 (k + 1) := by
  intro k hk
  interval_cases k <;> norm_num [U1e9, xh, l2hi, l2lo, rr]

theorem mono_1e9 : ∀ k < 30, U1e9 k ≤ U1e9 (k + 1) := by
  intro k hk
  interval_cases k <;> norm_num [U1e9]

/-- The constant at `L₀ = 20.72`: `≤ 0.12473` (exact value `0.124728311`). -/
theorem const_1e9 : dW / 6 * ((U1e9 0 - 1) + ∑ k ∈ range 30, (U1e9 (k + 1) - U1e9 k) / (Real.log 2 * 2 ^ (k + 1))) +
    100 / 189 * U1e9 30 / 2 ^ 30 ≤ 12473 / 100000 := by
  have hl2 := Real.log_two_gt_d9
  have hsum : ∑ k ∈ range 30, (U1e9 (k + 1) - U1e9 k) / (Real.log 2 * 2 ^ (k + 1)) ≤
      ∑ k ∈ range 30, (U1e9 (k + 1) - U1e9 k) / (0.6931471803 * 2 ^ (k + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    apply div_le_div_of_nonneg_left (sub_nonneg.2 (mono_1e9 k (mem_range.1 hk))) (by positivity)
    exact mul_le_mul_of_nonneg_right hl2.le (by positivity)
  have hval : dW / 6 * ((U1e9 0 - 1) + ∑ k ∈ range 30, (U1e9 (k + 1) - U1e9 k) / (0.6931471803 * 2 ^ (k + 1))) +
      100 / 189 * U1e9 30 / 2 ^ 30 ≤ 12473 / 100000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, U1e9, dW]
    norm_num
  have hd : 0 ≤ dW / 6 := by unfold dW; positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hd]

/-- **Sharper tail at `X ≥ 10 ^ 9`**: `Σ_{p∈S} ∏_{q∈S,q<p}(1+g q)/(p−1)^2 ≤ 0.12473/X`. -/
theorem tail2_1e9 {X : ℕ} (hX : 10 ^ 9 ≤ X) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ X < p) :
    ∑ p ∈ S, (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤
      12473 / 100000 / (X : ℝ) := by
  have hX8 : 10 ^ 8 ≤ X := le_trans (by norm_num) hX
  refine (tail2_generic hX8 (L₀ := 20.72) (by norm_num) (log_ge_1e9 hX) U1e9 30 (by norm_num) U0_1e9
    hstep_1e9 S hS).trans ?_
  exact div_le_div_of_nonneg_right (const_1e9) (Nat.cast_nonneg _)

/-- Grid values for `L₀ = 21.41` (`X ≥ 2 * 10 ^ 9`), rounded up to 12 digits. -/
noncomputable def U2e9 : ℕ → ℝ
  | 0 => 1.083959845848
  | 1 => 1.413051551668
  | 2 => 1.827029859535
  | 3 => 2.344171193591
  | 4 => 2.985957661696
  | 5 => 3.777519368733
  | 6 => 4.748122206565
  | 7 => 5.931704291087
  | 8 => 7.367464338922
  | 9 => 9.100505399468
  | 10 => 11.182537482289
  | 11 => 13.672642745147
  | 12 => 16.638107034354
  | 13 => 20.155321696503
  | 14 => 24.310759709043
  | 15 => 29.202030306552
  | 16 => 34.939016409915
  | 17 => 41.645099296944
  | 18 => 49.458475085250
  | 19 => 58.533567731345
  | 20 => 69.042543384099
  | 21 => 81.176931065668
  | 22 => 95.149354788914
  | 23 => 111.195382357132
  | 24 => 129.575496229540
  | 25 => 150.577191974490
  | 26 => 174.517209971698
  | 27 => 201.743906164983
  | 28 => 232.639767807990
  | 29 => 267.624080287186
  | 30 => 307.155751249038
  | _ => 0

theorem U0_2e9 : Real.exp (EE * KK / 21.41) ≤ U2e9 0 := by
  have hy : EE * KK / 21.41 ≤ 0.28768207246 * (6 * (1 + 1 / 10 ^ 7)) / 21.41 := by
    unfold KK
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right EE_le (by norm_num)
  refine (Real.exp_le_exp.2 hy).trans ?_
  refine (Real.exp_bound' (by norm_num) (by norm_num) (n := 10) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, U2e9]
  norm_num

theorem hstep_2e9 : ∀ k < 30, U2e9 k * (1 + xh 21.41 k) ^ 8 * (1 + rr * xh 21.41 k) ≤ U2e9 (k + 1) := by
  intro k hk
  interval_cases k <;> norm_num [U2e9, xh, l2hi, l2lo, rr]

theorem mono_2e9 : ∀ k < 30, U2e9 k ≤ U2e9 (k + 1) := by
  intro k hk
  interval_cases k <;> norm_num [U2e9]

/-- The constant at `L₀ = 21.41`: `≤ 0.11882` (exact value `0.118817627`). -/
theorem const_2e9 : dW / 6 * ((U2e9 0 - 1) + ∑ k ∈ range 30, (U2e9 (k + 1) - U2e9 k) / (Real.log 2 * 2 ^ (k + 1))) +
    100 / 189 * U2e9 30 / 2 ^ 30 ≤ 5941 / 50000 := by
  have hl2 := Real.log_two_gt_d9
  have hsum : ∑ k ∈ range 30, (U2e9 (k + 1) - U2e9 k) / (Real.log 2 * 2 ^ (k + 1)) ≤
      ∑ k ∈ range 30, (U2e9 (k + 1) - U2e9 k) / (0.6931471803 * 2 ^ (k + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    apply div_le_div_of_nonneg_left (sub_nonneg.2 (mono_2e9 k (mem_range.1 hk))) (by positivity)
    exact mul_le_mul_of_nonneg_right hl2.le (by positivity)
  have hval : dW / 6 * ((U2e9 0 - 1) + ∑ k ∈ range 30, (U2e9 (k + 1) - U2e9 k) / (0.6931471803 * 2 ^ (k + 1))) +
      100 / 189 * U2e9 30 / 2 ^ 30 ≤ 5941 / 50000 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, U2e9, dW]
    norm_num
  have hd : 0 ≤ dW / 6 := by unfold dW; positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hd]

/-- **Sharper tail at `X ≥ 2 * 10 ^ 9`**: `Σ_{p∈S} ∏_{q∈S,q<p}(1+g q)/(p−1)^2 ≤ 0.11882/X`. -/
theorem tail2_2e9 {X : ℕ} (hX : 2 * 10 ^ 9 ≤ X) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ X < p) :
    ∑ p ∈ S, (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤
      5941 / 50000 / (X : ℝ) := by
  have hX8 : 10 ^ 8 ≤ X := le_trans (by norm_num) hX
  refine (tail2_generic hX8 (L₀ := 21.41) (by norm_num) (log_ge_2e9 hX) U2e9 30 (by norm_num) U0_2e9
    hstep_2e9 S hS).trans ?_
  exact div_le_div_of_nonneg_right (const_2e9) (Nat.cast_nonneg _)

end MinModulus.Tail2
