import MinModulus.Checker2Math.SplitLawE
import MinModulus.CheckerMath.GFun

/-!
# `Checker2Math.SplitLawTau`: the τ-split bound (mathematics)

Owner: L2-B (lean2 stage 2). Namespace `MinModulus.Checker2Math.B`.

For `N1 = ⌈m/p⌉ ≤ 2` the hinge integrand is `(τ(s) − X)⁺` with `s = s_{PB}(v)` over the primes
`PB` below `p` (`Identities.hingeLoss_eq_tauSplit`). The checker splits the primes into `S` (the
primes `< YS`, law of `τ_S` by a weighted DP) and `L` (the rest; in the block phase `L` also
contains extra numbers, which only increases the bound), bounds `τ_L ≤ 2^e`, `e = Σ_L v_q`, and
integrates the `L`-coordinates by Fubini.

## Results
* `FB_le_weighted` (**weighted suffix bound**): if `W T ≥ T·P(τ_S = T, kept)` on `[0, TS]` and
  `Lb ≥ E[τ_S; lost]`, then for `0 ≤ y` and the integer `k` with `k − 1 ≤ y < k`:
  `E[(τ_S − y)⁺] ≤ Σ_{k ≤ T ≤ TS} (1 − y/T)·W T + Lb`.
* `FB_le_lost_of_ge` (edge case `y ≥ TS`): `E[(τ_S − y)⁺] ≤ Lb`.
  (The other edge case, `y ≤ 1`: `CheckerMath.FB_eq_of_le_one`.)
* `tauN_le_tauN_mul_two_pow` (**domination**): for `PB ⊆ S ∪ L`, `S ∩ L = ∅`:
  `τ_{PB}(v) ≤ τ_S(v)·2^{e_L(v)}`.
* `expect_hinge_tauSplit_le` (**the τ-split bound**): for a set `PB ⊆ S ∪ L` of primes,
  `S ∩ L = ∅`, admissible tilts on `S ∪ L`, `X ≥ 0`, every cap `γ`:
  `E_{PB}[(τ(s_{PB}) − X)⁺] ≤ Σ_{e ≤ NN} 2^e P_L(e, kept)·E_S[(τ_S − X/2^e)⁺] + E[τ_S]·E_L[2^e; lost]`.
-/

namespace MinModulus.Checker2Math.B

open Finset MinModulus.Smooth MinModulus.CheckerMath MinModulus.Checker2Math

/-! ### The weighted suffix bound for `E[(τ_S − y)⁺]` -/

/-- **Weighted suffix bound.** If `W T ≥ T·P(τ_S = T, kept)` for `T ≤ TS` and
`Lb ≥ E[τ_S; lost]`, then for `y ≥ 0` and an integer `k` with `k − 1 ≤ y < k`:
`E[(τ_S − y)⁺] ≤ Σ_{k ≤ T ≤ TS} (1 − y/T)·W T + Lb`. -/
theorem FB_le_weighted {S : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (TS : ℕ) (acut : ℕ → ℕ) (W : ℕ → ℝ)
    (hW : ∀ T ≤ TS, (T : ℝ) * lawKept S ν γ TS acut T ≤ W T) (Lb : ℝ)
    (hL : lostMass S ν γ TS acut ≤ Lb) {y : ℝ} (hy : 0 ≤ y) {k : ℕ}
    (hk1 : (k : ℝ) - 1 ≤ y) (hk2 : y < k) :
    FB S ν γ y ≤ ∑ T ∈ Ico k (TS + 1), (1 - y / T) * W T + Lb := by
  have hD : ∀ T ≤ TS, lawKept S ν γ TS acut T ≤ W T / T := by
    intro T hT
    rcases Nat.eq_zero_or_pos T with rfl | hT0
    · rw [lawKept_zero]
      simp
    · have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
      rw [le_div_iff₀ hT', mul_comm]
      exact hW T hT
  have h := FB_le_kept hν γ hy TS acut (fun T => W T / T) hD Lb hL
  refine h.trans (add_le_add (le_of_eq ?_) le_rfl)
  have e : ∀ T ∈ range (TS + 1), max 0 ((T : ℝ) - y) * (W T / T) =
      if k ≤ T then (1 - y / T) * W T else 0 := by
    intro T _
    split_ifs with hkT
    · have hkT' : (k : ℝ) ≤ T := by exact_mod_cast hkT
      have hT0 : (0 : ℝ) < T := by linarith
      rw [max_eq_right (by linarith)]
      field_simp
    · have hT1 : (T : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.lt_of_not_le hkT)
      rw [max_eq_left (by linarith), zero_mul]
  rw [sum_congr rfl e, ← sum_filter]
  congr 1
  ext T
  simp only [mem_filter, mem_range, mem_Ico]
  omega

/-- **Edge case `y ≥ TS`**: every kept `τ_S` is `≤ TS ≤ y`, so `E[(τ_S − y)⁺] ≤ E[τ_S; lost]`. -/
theorem FB_le_lost_of_ge {S : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (TS : ℕ) (acut : ℕ → ℕ) (Lb : ℝ) (hL : lostMass S ν γ TS acut ≤ Lb) {y : ℝ}
    (hy : (TS : ℝ) ≤ y) : FB S ν γ y ≤ Lb := by
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg TS) hy
  have h := FB_le_kept hν γ hy0 TS acut (lawKept S ν γ TS acut) (fun T _ => le_rfl) Lb hL
  have h0 : ∑ T ∈ range (TS + 1), max 0 ((T : ℝ) - y) * lawKept S ν γ TS acut T = 0 := by
    refine sum_eq_zero fun T hT => ?_
    have : (T : ℝ) ≤ TS := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hT)
    rw [max_eq_left (by linarith), zero_mul]
  linarith

/-! ### Domination `τ_{PB} ≤ τ_S · 2^{e_L}` -/

/-- `τ_L(v) ≤ 2^{e_L(v)}` (`a + 1 ≤ 2^a`), for any set `L` of numbers. -/
theorem tauN_le_two_pow_estat (L : Finset ℕ) (v : ℕ → ℕ) : tauN L v ≤ 2 ^ estat L v := by
  unfold tauN estat
  rw [← prod_pow_eq_pow_sum]
  exact prod_le_prod fun q _ => Nat.lt_two_pow_self

/-- **Domination**: for `PB ⊆ S ∪ L` with `S ∩ L = ∅`, `τ_{PB}(v) ≤ τ_S(v)·2^{e_L(v)}`. -/
theorem tauN_le_tauN_mul_two_pow {PB S L : Finset ℕ} (hsub : PB ⊆ S ∪ L) (hSL : Disjoint S L)
    (v : ℕ → ℕ) : tauN PB v ≤ tauN S v * 2 ^ estat L v := by
  have h1 : tauN PB v ≤ tauN (S ∪ L) v :=
    prod_le_prod_of_subset_of_one_le hsub fun q _ _ => Nat.succ_pos (v q)
  have h2 : tauN (S ∪ L) v = tauN S v * tauN L v := prod_union hSL
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_left _ (tauN_le_two_pow_estat L v))

/-! ### The τ-split bound -/

/-- `max 0 (t·c − X) = c · max 0 (t − X/c)` for `c > 0`. -/
theorem max_zero_mul_sub_eq {t c X : ℝ} (hc : 0 < c) :
    max 0 (t * c - X) = c * max 0 (t - X / c) := by
  have e : t * c - X = c * (t - X / c) := by
    field_simp
  rw [e, mul_max_of_nonneg _ _ hc.le, mul_zero]

/-- **The τ-split bound** (every cap `γ`). Let `PB` be a set of primes, `PB ⊆ S ∪ L` with `S` and
`L` disjoint, tilts admissible on `S ∪ L`, and `X ≥ 0`. Then
`E_{PB}[(τ(s_{PB}) − X)⁺] ≤ Σ_{e ≤ NN} 2^e P_L(e, kept)·E_S[(τ_S − X/2^e)⁺] + E[τ_S]·E_L[2^e; lost]`. -/
theorem expect_hinge_tauSplit_le {PB S L : Finset ℕ} {ν : ℕ → ℝ} (hPB : ∀ q ∈ PB, q.Prime)
    (hsub : PB ⊆ S ∪ L) (hSL : Disjoint S L) (hν : ∀ q ∈ S ∪ L, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) {X : ℝ} (hX : 0 ≤ X) (NN : ℕ) (acut : ℕ → ℕ) :
    expect PB ν γ (fun v => max 0 (((smooth PB v).divisors.card : ℝ) - X)) ≤
      ∑ e ∈ range (NN + 1), (2 : ℝ) ^ e * lawE L ν γ NN acut e * FB S ν γ (X / 2 ^ e) +
        meanTau S ν γ * lostE L ν γ NN acut := by
  have hνS : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q := fun q hq => hν q (mem_union_left L hq)
  have hνL : ∀ q ∈ L, 0 ≤ ν q ∧ ν q ≤ q := fun q hq => hν q (mem_union_right S hq)
  -- (A) marginalization: `E_{PB} = E_{S ∪ L}` for a function of the `PB`-coordinates
  have hA : expect PB ν γ (fun v => max 0 (((smooth PB v).divisors.card : ℝ) - X)) =
      expect (S ∪ L) ν γ (fun v => max 0 (((smooth PB v).divisors.card : ℝ) - X)) := by
    refine (expect_eq_of_subset hsub ν γ fun v w hvw => ?_).symm
    have : smooth PB v = smooth PB w := prod_congr rfl fun q hq => by rw [hvw q hq]
    rw [this]
  -- (B) domination
  set g : (ℕ → ℕ) → ℝ := fun v => max 0 ((tauN S v : ℝ) * 2 ^ estat L v - X) with hg
  have hB : expect (S ∪ L) ν γ (fun v => max 0 (((smooth PB v).divisors.card : ℝ) - X)) ≤
      expect (S ∪ L) ν γ g := by
    refine expect_mono hν fun v _ => max_le_max le_rfl (sub_le_sub_right ?_ X)
    rw [card_divisors_smooth_eq_tauN hPB v]
    have := tauN_le_tauN_mul_two_pow hsub hSL v
    exact_mod_cast this
  -- (C) Fubini, the `L`-coordinates outside
  have hC : expect (S ∪ L) ν γ g =
      expect L ν γ (fun w => (2 : ℝ) ^ estat L w * FB S ν γ (X / 2 ^ estat L w)) := by
    rw [union_comm, expect_union hSL.symm]
    refine expect_congr_fun fun w hw => ?_
    have hw0 : ∀ q ∈ S, w q = 0 := fun q hq =>
      (mem_box.1 hw).2 q (fun hqL => disjoint_left.1 hSL hq hqL)
    unfold FB
    rw [← expect_const_mul]
    refine expect_congr_fun fun v hv => ?_
    have hv0 : ∀ q ∈ L, v q = 0 := fun q hq =>
      (mem_box.1 hv).2 q (fun hqS => disjoint_left.1 hSL hqS hq)
    have h1 : tauN S (w + v) = tauN S v :=
      prod_congr rfl fun q hq => by simp [hw0 q hq]
    have h2 : estat L (w + v) = estat L w :=
      sum_congr rfl fun q hq => by simp [hv0 q hq]
    simp only [hg, h1, h2]
    exact max_zero_mul_sub_eq (by positivity)
  -- (D) kept / lost decomposition of the `L`-law
  rw [hA]
  refine hB.trans ?_
  rw [hC, expect_estat_eq L ν γ NN acut (fun e => (2 : ℝ) ^ e * FB S ν γ (X / 2 ^ e))]
  refine add_le_add (le_of_eq (sum_congr rfl fun e _ => by ring)) ?_
  have hlost : expect L ν γ (fun w => if KeptE L NN acut w then 0 else
        (2 : ℝ) ^ estat L w * FB S ν γ (X / 2 ^ estat L w)) ≤
      expect L ν γ (fun w => (if KeptE L NN acut w then 0 else (2 : ℝ) ^ estat L w) *
        meanTau S ν γ) := by
    refine expect_mono hνL fun w _ => ?_
    split_ifs
    · simp
    · exact mul_le_mul_of_nonneg_left (FB_le_meanTau hνS γ (by positivity)) (by positivity)
  rw [expect_mul_const] at hlost
  unfold lostE
  linarith

end MinModulus.Checker2Math.B
