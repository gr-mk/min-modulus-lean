import MinModulus.Tail2.Outer
import MinModulus.Tail.Main
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# Tail2.Bound: the sharper tail bound (generic form)

STATUS: complete, no `sorry` (L2-T). Imports `Tail2.Outer`, `Tail.Main` (read-only, for the far part)
and Mathlib.

## Main result
`tail2_generic`: for `10^8 ≤ X`, `0 < L₀ ≤ log X`, `1 ≤ K` and grid values `U : ℕ → ℝ` with
* `exp(EE·KK/L₀) ≤ U 0` and
* `U k · (1 + x̂ₖ)^8 · (1 + rr·x̂ₖ) ≤ U (k+1)` for `k < K`, `x̂ₖ = ℓ⁺/(L₀ + k ℓ⁻)`
  (`ℓ⁻ = 0.6931471803 < log 2 < ℓ⁺ = 0.6931471808`, `rr = 0.317779002 ≥ 2 cA KK − 8`),
every finite set `S` of primes `> X` satisfies
`Σ_{p∈S} ∏_{q∈S, q<p} (1 + g q)/(p−1)^2 ≤
   (dW/6 · ((U 0 − 1) + Σ_{k<K} (U(k+1) − U k)/(log 2 · 2^(k+1))) + (100/189) U K / 2^K) / X`.

## Proof
1. `Pn_le`: `P_S(n) ≤ exp(Σ g) ≤ C₀ (1 + log(n/X)/L)^a` with `L = log X`, `a = 2 cA KK`,
   `C₀ = exp(EE KK/L)` (`Inner.inner_bound`).
2. `grid_le`: `C₀ (1 + k log 2/L)^a ≤ U k` by induction on `k` (`(1+x)^a ≤ (1+x)^8 (1 + (a−8) x)`,
   Bernoulli for the exponent `a − 8 ∈ [0, 1]`).
3. `Outer.sum_term_eq` + `Outer.outer_chain` for `S ∩ (X, X 2^K]`; the boundary term cancels with
   `−(U K − 1)/(X 2^K)`.
4. The primes of `S` above `X 2^K`: `P_S(X 2^K) ≤ U K` times the old bound
   `Tail.tail_bound_g` at `X 2^K` (`≤ 100/(189 X 2^K)`).
-/

namespace MinModulus.Tail2

open Finset Real

/-- Upper bound `0.6931471808` for `log 2` (`Real.log_two_lt_d9`). -/
noncomputable def l2hi : ℝ := 0.6931471808

/-- Lower bound `0.6931471803` for `log 2` (`Real.log_two_gt_d9`). -/
noncomputable def l2lo : ℝ := 0.6931471803

/-- `rr = 0.317779002 ≥ 2 cA KK − 8`. -/
noncomputable def rr : ℝ := 0.317779002

/-- The grid ratio bound `x̂ₖ = ℓ⁺/(L₀ + k ℓ⁻) ≥ log 2/(L + k log 2)`. -/
noncomputable def xh (L₀ : ℝ) (k : ℕ) : ℝ := l2hi / (L₀ + k * l2lo)

/-- The exponent `a = 2 cA KK ≈ 8.3178`. -/
noncomputable def aE : ℝ := 2 * cA * KK

theorem aE_bounds : 8 ≤ aE ∧ aE - 8 ≤ rr := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  unfold aE cA KK rr
  constructor <;> nlinarith

theorem Tail_g_eq (q : ℕ) : Tail.g q = gR q := rfl

/-- **Step 1.** `P_S(n) ≤ C₀ (1 + log(n/X)/L)^a` for `n ≥ X`. -/
theorem Pn_le {S : Finset ℕ} {X : ℕ} (hX : 10 ^ 8 ≤ X) (hS : ∀ p ∈ S, p.Prime ∧ X < p)
    {n : ℕ} (hXn : X ≤ n) :
    Pn S n ≤ Real.exp (EE * KK / Real.log X) *
      (1 + Real.log (n / X) / Real.log X) ^ aE := by
  have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXnr : (X : ℝ) ≤ n := by exact_mod_cast hXn
  have hnpos : (0 : ℝ) < n := by linarith
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hLn : 0 < Real.log n := Real.log_pos (by linarith)
  -- product ≤ exp(sum)
  have h1 : Pn S n ≤ Real.exp (∑ q ∈ S.filter (· ≤ n), gR q) := by
    unfold Pn
    rw [Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro q hq
      have := gR_nonneg (s := (q : ℝ)) (by exact_mod_cast (hS q (mem_filter.1 hq).1).1.one_lt.le)
      linarith
    · intro q _
      rw [add_comm]
      exact Real.add_one_le_exp _
  -- sum over S ≤ sum over the primes of (X, n]
  have h2 : ∑ q ∈ S.filter (· ≤ n), gR q ≤ ∑ q ∈ Ioc X n, if q.Prime then gR q else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [mem_filter] at hq ⊢
      exact ⟨mem_Ioc.2 ⟨(hS q hq.1).2, hq.2⟩, (hS q hq.1).1⟩
    · intro q hq _
      rw [mem_filter] at hq
      exact gR_nonneg (by exact_mod_cast hq.2.one_lt.le)
  have h3 := inner_bound hX hXn
  -- rewrite the bound as C₀ (log n / log X)^a
  have hlogn : Real.log n = Real.log X + Real.log (n / X) := by
    rw [Real.log_div hnpos.ne' hXpos.ne']; ring
  have hratio : 1 + Real.log (n / X) / Real.log X = Real.log n / Real.log X := by
    rw [hlogn]; field_simp
  have hpow : (1 + Real.log (n / X) / Real.log X) ^ aE =
      Real.exp (aE * (Real.log (Real.log n) - Real.log (Real.log X))) := by
    rw [hratio, Real.rpow_def_of_pos (by positivity), Real.log_div hLn.ne' hLX.ne']
    ring_nf
  rw [hpow, ← Real.exp_add]
  refine h1.trans (Real.exp_le_exp.2 (h2.trans (h3.trans (le_of_eq ?_))))
  unfold aE
  ring

/-- **Step 2.** The grid values: `C₀ (1 + k log 2/L)^a ≤ U k` for `k ≤ K`. -/
theorem grid_le {X : ℕ} {L₀ : ℝ} (hL₀ : 0 < L₀) (hLX : L₀ ≤ Real.log X)
    (U : ℕ → ℝ) (K : ℕ) (hU0 : Real.exp (EE * KK / L₀) ≤ U 0)
    (hstep : ∀ k < K, U k * (1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k) ≤ U (k + 1)) :
    ∀ k ≤ K, Real.exp (EE * KK / Real.log X) * (1 + k * Real.log 2 / Real.log X) ^ aE ≤ U k := by
  have hl2lo := Real.log_two_gt_d9
  have hl2hi := Real.log_two_lt_d9
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < Real.log X := hL₀.trans_le hLX
  have ha := aE_bounds
  set L := Real.log X with hLdef
  set C₀ := Real.exp (EE * KK / L) with hC₀
  intro k
  induction k with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, Real.one_rpow, mul_one]
    refine le_trans (Real.exp_le_exp.2 ?_) hU0
    have hEK : 0 < EE * KK := mul_pos EE_pos KK_pos
    exact div_le_div_of_nonneg_left hEK.le hL₀ hLX
  | succ k ih =>
    intro hk
    have hIH := ih (by omega)
    set x := Real.log 2 / (L + k * Real.log 2) with hx
    have hden : 0 < L + k * Real.log 2 := by positivity
    have hx0 : 0 ≤ x := div_nonneg hl2.le hden.le
    have hsplit : 1 + ((k + 1 : ℕ) : ℝ) * Real.log 2 / L = (1 + k * Real.log 2 / L) * (1 + x) := by
      rw [hx]; push_cast; field_simp; ring
    have hbase : 0 ≤ 1 + k * Real.log 2 / L := by positivity
    rw [hsplit, Real.mul_rpow hbase (by linarith)]
    -- (1 + x)^a ≤ (1 + x)^8 (1 + (a − 8) x)
    have hxa : (1 + x) ^ aE ≤ (1 + x) ^ 8 * (1 + (aE - 8) * x) := by
      have e : aE = (8 : ℕ) + (aE - 8) := by push_cast; ring
      rw [e, Real.rpow_add (by linarith), Real.rpow_natCast]
      rw [show ((8 : ℕ) : ℝ) + (aE - 8) - 8 = aE - 8 by push_cast; ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact rpow_one_add_le_one_add_mul_self (by linarith) (by linarith [ha.1]) (by linarith [ha.2, show rr < 1 by unfold rr; norm_num])
    -- x ≤ x̂
    have hxx : x ≤ xh L₀ k := by
      rw [hx]; unfold xh l2hi l2lo
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hl2lo.le hk0]
    have hmono : (1 + x) ^ 8 * (1 + (aE - 8) * x) ≤ (1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k) := by
      have hxh0 : 0 ≤ xh L₀ k := hx0.trans hxx
      apply mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 8)
      · nlinarith [ha.1, ha.2, mul_le_mul_of_nonneg_left hxx (by linarith [ha.1] : (0 : ℝ) ≤ aE - 8)]
      · nlinarith [ha.1]
      · positivity
    have hU0' : 0 ≤ U k := le_trans (by positivity) hIH
    calc C₀ * ((1 + k * Real.log 2 / L) ^ aE * (1 + x) ^ aE)
        = (C₀ * (1 + k * Real.log 2 / L) ^ aE) * (1 + x) ^ aE := by ring
      _ ≤ U k * ((1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k)) := by
          apply mul_le_mul hIH (hxa.trans hmono) (by positivity) hU0'
      _ = U k * (1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k) := by ring
      _ ≤ U (k + 1) := hstep k (by omega)

/-- **The sharper tail bound (generic form).** -/
theorem tail2_generic {X : ℕ} (hX : 10 ^ 8 ≤ X) {L₀ : ℝ} (hL₀ : 0 < L₀) (hLX : L₀ ≤ Real.log X)
    (U : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K) (hU0 : Real.exp (EE * KK / L₀) ≤ U 0)
    (hstep : ∀ k < K, U k * (1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k) ≤ U (k + 1))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ X < p) :
    ∑ p ∈ S, (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤
      (dW / 6 * ((U 0 - 1) + ∑ k ∈ range K, (U (k + 1) - U k) / (Real.log 2 * 2 ^ (k + 1))) +
        100 / 189 * U K / 2 ^ K) / X := by
  have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log X := hL₀.trans_le hLX
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha := aE_bounds
  have hS' : ∀ p ∈ S, X < p := fun p hp => (hS p hp).2
  have hgrid := grid_le hL₀ hLX U K hU0 hstep
  have hUm : ∀ k < K, U k ≤ U (k + 1) := by
    intro k hk
    have h1 := hgrid k hk.le
    have hU0' : 0 ≤ U k := le_trans (by positivity) h1
    have hxh : 0 ≤ xh L₀ k := by unfold xh l2hi l2lo; positivity
    have hf : 1 ≤ (1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k) := by
      have h8 : 1 ≤ (1 + xh L₀ k) ^ 8 := one_le_pow₀ (by linarith)
      have hr0 : 0 ≤ rr := by unfold rr; norm_num
      have hr : 1 ≤ 1 + rr * xh L₀ k := by nlinarith [mul_nonneg hr0 hxh]
      nlinarith
    calc U k = U k * 1 := by ring
      _ ≤ U k * ((1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k)) := mul_le_mul_of_nonneg_left hf hU0'
      _ = U k * (1 + xh L₀ k) ^ 8 * (1 + rr * xh L₀ k) := by ring
      _ ≤ U (k + 1) := hstep k hk
  have hPn : ∀ n : ℕ, X ≤ n → Pn S n ≤
      Real.exp (EE * KK / Real.log X) * (1 + Real.log (n / X) / Real.log X) ^ aE :=
    fun n hn => Pn_le hX hS hn
  have hchain := outer_chain hX hS' (Real.exp_pos _).le (by linarith [ha.1]) hL hPn U K
    hgrid hUm K le_rfl
  set tK := X * 2 ^ K with htK
  have htKr : ((tK : ℕ) : ℝ) = (X : ℝ) * 2 ^ K := by rw [htK]; push_cast; ring
  have htK8 : (10 : ℝ) ^ 8 ≤ ((tK : ℕ) : ℝ) := by
    rw [htKr]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (by norm_num) (n := K)]
  have hXtK : X ≤ tK := Nat.le_mul_of_pos_right X (by positivity)
  -- `P_S(X 2^K) ≤ U K`
  have hPtK : Pn S tK ≤ U K := by
    have h1 := Pn_le hX hS hXtK
    have hlog : Real.log ((tK : ℝ) / X) = K * Real.log 2 := by
      rw [htKr, show (X : ℝ) * 2 ^ K / X = 2 ^ K by field_simp, Real.log_pow]
    rw [hlog] at h1
    exact h1.trans (hgrid K le_rfl)
  have hS1 : ∀ p ∈ S, 1 ≤ p := fun p hp => by have := hS' p hp; omega
  have hP1 : 0 ≤ Pn S tK - 1 := by have := one_le_Pn hS1 tK; linarith
  have hUK1 : 0 ≤ U K - 1 := by have := one_le_Pn hS1 tK; linarith
  -- part 1: the primes `≤ X 2^K`
  have hpart1 : ∑ p ∈ S.filter (· ≤ tK), (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤
      dW / 6 * ((U 0 - 1) / X +
        ∑ k ∈ range K, (U (k + 1) - U k) / (Real.log 2 * ((X : ℝ) * 2 ^ (k + 1)))) := by
    rw [sum_term_eq hS' (by omega) tK]
    refine hchain.trans ?_
    have hw := wR_le htK8
    have hbd : (Pn S tK - 1) * wR ((tK : ℕ) : ℝ) ≤ dW / 6 * ((U K - 1) / ((X : ℝ) * 2 ^ K)) := by
      calc (Pn S tK - 1) * wR ((tK : ℕ) : ℝ) ≤ (U K - 1) * (dW / 6 * (1 / ((tK : ℕ) : ℝ))) :=
            mul_le_mul (by linarith) hw (wR_nonneg (by linarith)) hUK1
        _ = dW / 6 * ((U K - 1) / ((X : ℝ) * 2 ^ K)) := by rw [htKr]; ring
    have hd : 0 < dW / 6 := by have := dW_pos; positivity
    nlinarith
  -- part 2: the primes `> X 2^K`, by the old bound at `X 2^K`
  set S' := S.filter (fun p => ¬ p ≤ tK) with hS'def
  have hS'p : ∀ p ∈ S', p.Prime ∧ tK < p := by
    intro p hp
    rw [hS'def, mem_filter] at hp
    exact ⟨(hS p hp.1).1, by omega⟩
  have htK27 : 2 ^ 27 ≤ tK := by
    have : 2 ^ 27 ≤ X * 2 := by omega
    exact this.trans (Nat.mul_le_mul_left _ (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK))
  have hold := Tail.tail_bound_g tK htK27 S' hS'p
  have hfac : ∀ p ∈ S', ∏ q ∈ S.filter (· < p), (1 + gR q) =
      Pn S tK * ∏ q ∈ S'.filter (· < p), (1 + gR q) := by
    intro p hp
    have hp' := (hS'p p hp).2
    unfold Pn
    rw [← Finset.prod_union]
    · congr 1
      ext q
      simp only [mem_filter, mem_union, hS'def]
      constructor
      · rintro ⟨hq, hqp⟩
        by_cases h : q ≤ tK
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨⟨hq, h⟩, hqp⟩
      · rintro (⟨hq, h⟩ | ⟨⟨hq, h⟩, hqp⟩)
        · exact ⟨hq, by omega⟩
        · exact ⟨hq, hqp⟩
    · rw [Finset.disjoint_left]
      intro q hq hq'
      simp only [mem_filter, hS'def] at hq hq'
      exact hq'.1.2 hq.2
  have hpart2 : ∑ p ∈ S', (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤
      U K * (100 / (189 * ((tK : ℕ) : ℝ))) := by
    rw [Finset.sum_congr rfl fun p hp => by rw [hfac p hp, mul_div_assoc], ← Finset.mul_sum]
    have hsum0 : 0 ≤ ∑ p ∈ S', (∏ q ∈ S'.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 := by
      apply Finset.sum_nonneg
      intro p hp
      apply div_nonneg _ (sq_nonneg _)
      apply Finset.prod_nonneg
      intro q hq
      have := gR_nonneg (s := (q : ℝ)) (by
        exact_mod_cast (hS'p q (mem_filter.1 hq).1).1.one_lt.le)
      linarith
    have hold' : ∑ p ∈ S', (∏ q ∈ S'.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤
        100 / (189 * ((tK : ℕ) : ℝ)) := hold
    have hPn0 : 0 ≤ Pn S tK := by have := one_le_Pn hS1 tK; linarith
    exact mul_le_mul hPtK hold' hsum0 (by linarith)
  -- combine
  rw [← Finset.sum_filter_add_sum_filter_not S (· ≤ tK)]
  have e1 : ∑ k ∈ range K, (U (k + 1) - U k) / (Real.log 2 * ((X : ℝ) * 2 ^ (k + 1))) =
      (∑ k ∈ range K, (U (k + 1) - U k) / (Real.log 2 * 2 ^ (k + 1))) / X := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  have e2 : U K * (100 / (189 * ((tK : ℕ) : ℝ))) = 100 / 189 * U K / 2 ^ K / X := by
    rw [htKr]; field_simp
  rw [e1] at hpart1
  rw [e2] at hpart2
  have e3 : (dW / 6 * ((U 0 - 1) + ∑ k ∈ range K, (U (k + 1) - U k) / (Real.log 2 * 2 ^ (k + 1))) +
        100 / 189 * U K / 2 ^ K) / X =
      dW / 6 * ((U 0 - 1) / X + (∑ k ∈ range K, (U (k + 1) - U k) / (Real.log 2 * 2 ^ (k + 1))) / X) +
        100 / 189 * U K / 2 ^ K / X := by
    field_simp
  rw [e3]
  linarith

end MinModulus.Tail2
