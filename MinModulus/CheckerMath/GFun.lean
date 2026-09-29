import MinModulus.CheckerMath.TauLaw

/-!
# `CheckerMath`, part 2: the functions `FB` and `G` of the comparison bound

For a finite set `B` of primes (the "B part"), tilts `ν`, caps `γ`:
* `meanTau B ν γ = E_B[τ_B]`;
* `FB B ν γ c = E_B[(τ_B - c)^+]`;
* `GB B ν γ t α u = E_B[(u + (τ_B - 1) α - t)^+]` (`G(k, u)` of `rigcert.c` is
  `GB … t (k/(p-1)) u`).

## Identities and monotonicity
* `GB_eq_mul_FB`: `G(α, u) = α · FB(1 + (t - u)/α)` for `α > 0` (`c = 1 + (t-u)(p-1)/k`);
* `GB_eq_of_le`: `G(α, u) = u - t + (E[τ_B] - 1) α` for `u ≥ t`, `α ≥ 0`;
* `FB_eq_of_le_one`: `FB(c) = E[τ_B] - c` for `c ≤ 1`;
* `GB_mono` (nondecreasing in `α` and `u`), `FB_antitone`, `GB_diag_le`
  (`G(α, α) ≤ α E[τ_B]` for `t ≥ 0`), nonnegativity.

## Upper bounds for `FB` from a truncated DP (for every cap `γ`)
With `D T ≥ P(τ_B = T, kept)` for `T ≤ TM` (`TauLaw.lawKept`):
* `FB_le_kept` (`rigcert.c`): `FB(c) ≤ Σ_{T ≤ TM} (T - c)^+ D[T] + L` for `c ≥ 0`,
  `L ≥ E[τ_B; lost]`;
* `FB_le_lowerTail` (Lean checker, `fbUp`): `FB(c) ≤ EB - c + Σ_{T ≤ TM} (c - T)^+ D[T] + c·P`
  for `0 ≤ c ≤ TM + 1`, `EB ≥ E[τ_B]`, `P ≥ P(∃ q, v_q > acut q)`.

## Suffix / prefix sums (pure algebra, any `D`)
* `sum_hinge_eq_suffix` (`rigcert.c`'s `FBup`): for an integer `k` with `k - 1 ≤ c ≤ k`,
  `Σ_{T ≤ TM} (T - c)^+ D[T] = SS[k+1] + (k - c) S0[k]` with the suffix sums
  `S0[j] = Σ_{j ≤ T ≤ TM} D[T]`, `SS[j] = Σ_{j ≤ i ≤ TM} S0[i]` (`sufS0`, `sufSS`, and their
  recursions `sufS0_eq`, `sufSS_eq`). rigcert takes `k = ⌊c⌋ + 1`.
* `sum_lowerHinge_eq_prefix` (checker's `fbTable`/`fbUp`): for `k = ⌊c⌋ ≤ TM`,
  `Σ_{T ≤ TM} (c - T)^+ D[T] = Σ_{i < k} P0[i] + (c - k) P0[k]` with `P0[j] = Σ_{T ≤ j} D[T]`
  (`preS0`).
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth

/-- `E_B[τ_B]`. -/
noncomputable def meanTau (B : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) : ℝ :=
  expect B ν γ (fun w => (tauN B w : ℝ))

/-- `FB(c) = E_B[(τ_B - c)^+]`. -/
noncomputable def FB (B : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (c : ℝ) : ℝ :=
  expect B ν γ (fun w => max 0 ((tauN B w : ℝ) - c))

/-- `G(α, u) = E_B[(u + (τ_B - 1) α - t)^+]`. -/
noncomputable def GB (B : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (t α u : ℝ) : ℝ :=
  expect B ν γ (fun w => max 0 (u + ((tauN B w : ℝ) - 1) * α - t))

variable {B : Finset ℕ} {ν : ℕ → ℝ} {γ : ℕ → ℕ}

/-! ### Basic properties -/

theorem meanTau_nonneg (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) : 0 ≤ meanTau B ν γ :=
  expect_nonneg hν fun w _ => tauN_real_nonneg B w

/-- `E_γ[τ_B] ≤ ∏_{q ∈ B} (1 + ν_q/(q-1))`, every cap. -/
theorem meanTau_le (hB : ∀ q ∈ B, 1 < q) (hν : ∀ q ∈ B, 0 ≤ ν q) (γ : ℕ → ℕ) :
    meanTau B ν γ ≤ ∏ q ∈ B, (1 + ν q / ((q : ℝ) - 1)) :=
  expect_tauN_le hB hν γ

/-- `E_γ[τ_B]` is nondecreasing in the caps. -/
theorem meanTau_mono_cap (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) {γ γ' : ℕ → ℕ}
    (hγ : ∀ q ∈ B, γ q ≤ γ' q) : meanTau B ν γ ≤ meanTau B ν γ' :=
  expect_mono_cap hν hγ fun v w hvw => by
    exact_mod_cast tauN_mono B fun q _ => hvw q

/-- **Lost mass from lower bounds** (the Lean checker's `tailA = EA - Σ_k k·dn[k]`): if
`EA ≥ E[τ]` and `dn T ≤ P(τ = T, kept)` for `T ≤ TM`, then
`E[τ; lost] ≤ EA - Σ_{T ≤ TM} T · dn[T]`. -/
theorem lostMass_le_of_lower (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ) (EA : ℝ)
    (hEA : meanTau B ν γ ≤ EA) (dn : ℕ → ℝ) (hdn : ∀ T ≤ TM, dn T ≤ lawKept B ν γ TM acut T) :
    lostMass B ν γ TM acut ≤ EA - ∑ T ∈ range (TM + 1), (T : ℝ) * dn T := by
  have h := expect_tauN_eq B ν γ TM acut
  have hs : ∑ T ∈ range (TM + 1), (T : ℝ) * dn T ≤
      ∑ T ∈ range (TM + 1), (T : ℝ) * lawKept B ν γ TM acut T :=
    sum_le_sum fun T hT => mul_le_mul_of_nonneg_left
      (hdn T (Nat.lt_succ_iff.1 (mem_range.1 hT))) (Nat.cast_nonneg T)
  unfold meanTau at hEA
  linarith

theorem FB_nonneg (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (c : ℝ) : 0 ≤ FB B ν γ c :=
  expect_nonneg hν fun _ _ => le_max_left _ _

theorem GB_nonneg (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (t α u : ℝ) :
    0 ≤ GB B ν γ t α u :=
  expect_nonneg hν fun _ _ => le_max_left _ _

/-- `FB` is nonincreasing in `c`. -/
theorem FB_antitone (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {c c' : ℝ} (h : c ≤ c') :
    FB B ν γ c' ≤ FB B ν γ c :=
  expect_mono hν fun _ _ => max_le_max le_rfl (by linarith)

/-- `G` is nondecreasing in `α` and in `u` (because `τ_B ≥ 1`). -/
theorem GB_mono (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (t : ℝ) {α α' u u' : ℝ}
    (hα : α ≤ α') (hu : u ≤ u') : GB B ν γ t α u ≤ GB B ν γ t α' u' := by
  refine expect_mono hν fun w _ => max_le_max le_rfl ?_
  have h1 : (0 : ℝ) ≤ (tauN B w : ℝ) - 1 := by linarith [one_le_tauN_real B w]
  have := mul_le_mul_of_nonneg_left hα h1
  linarith

/-- `FB(c) = E[τ_B] - c` for `c ≤ 1`. -/
theorem FB_eq_of_le_one (γ : ℕ → ℕ) {c : ℝ} (hc : c ≤ 1) : FB B ν γ c = meanTau B ν γ - c := by
  unfold FB meanTau
  rw [← expect_const B ν γ c, ← expect_sub]
  refine expect_congr_fun fun w _ => ?_
  rw [expect_const]
  exact max_eq_right (by linarith [one_le_tauN_real B w])

/-- **`G = α · FB`**: for `α > 0`, `G(α, u) = α · FB(1 + (t - u)/α)`. With `α = k/(p-1)` this is
`(k/(p-1)) · E_B[(τ_B - c)^+]`, `c = 1 + (t - u)(p - 1)/k`. -/
theorem GB_eq_mul_FB (γ : ℕ → ℕ) {α : ℝ} (hα : 0 < α) (t u : ℝ) :
    GB B ν γ t α u = α * FB B ν γ (1 + (t - u) / α) := by
  unfold GB FB
  rw [← expect_const_mul]
  refine expect_congr_fun fun w _ => ?_
  have e : u + ((tauN B w : ℝ) - 1) * α - t = α * ((tauN B w : ℝ) - (1 + (t - u) / α)) := by
    field_simp
    ring
  rw [e, mul_max_of_nonneg _ _ hα.le, mul_zero]

/-- For `u ≥ t` (and `α ≥ 0`) no positive part is needed:
`G(α, u) = u - t + (E[τ_B] - 1) α`. -/
theorem GB_eq_of_le (γ : ℕ → ℕ) {α : ℝ} (hα : 0 ≤ α) {t u : ℝ} (htu : t ≤ u) :
    GB B ν γ t α u = u - t + (meanTau B ν γ - 1) * α := by
  unfold GB meanTau
  have h : ∀ w, max 0 (u + ((tauN B w : ℝ) - 1) * α - t) =
      (u - t - α) + α * (tauN B w : ℝ) := by
    intro w
    have h1 : (0 : ℝ) ≤ ((tauN B w : ℝ) - 1) * α :=
      mul_nonneg (by linarith [one_le_tauN_real B w]) hα
    rw [max_eq_right (by linarith)]
    ring
  simp_rw [h]
  rw [expect_add, expect_const, expect_const_mul]
  ring

/-- `G(α, α) ≤ α E[τ_B]` for `α, t ≥ 0` (used for the lost `τ_A`-mass). -/
theorem GB_diag_le (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {α t : ℝ} (hα : 0 ≤ α)
    (ht : 0 ≤ t) : GB B ν γ t α α ≤ α * meanTau B ν γ := by
  unfold GB meanTau
  rw [← expect_const_mul]
  refine expect_mono hν fun w _ => max_le (mul_nonneg hα (tauN_real_nonneg B w)) ?_
  nlinarith

/-- `G(α, α) ≤ α · EB` for `α, t ≥ 0` and `E[τ_B] ≤ EB` (`rigcert.c`'s shortcut
`G(k, k/(p-1)) ≤ k EB/(p-1)`). -/
theorem GB_diag_le_of (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {α t EB : ℝ} (hα : 0 ≤ α)
    (ht : 0 ≤ t) (hEB : meanTau B ν γ ≤ EB) : GB B ν γ t α α ≤ α * EB :=
  (GB_diag_le hν γ hα ht).trans (mul_le_mul_of_nonneg_left hEB hα)

/-! ### Upper bounds for `FB` from a truncated DP -/

/-- **`FB` bound, lost-mass form** (`rigcert.c`): for `c ≥ 0`, if `D T ≥ P(τ_B = T, kept)` for
`T ≤ TM` and `L ≥ E[τ_B; lost]`, then `FB(c) ≤ Σ_{T ≤ TM} (T - c)^+ D[T] + L`. -/
theorem FB_le_kept (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (TM : ℕ) (acut : ℕ → ℕ) (D : ℕ → ℝ) (hD : ∀ T ≤ TM, lawKept B ν γ TM acut T ≤ D T)
    (L : ℝ) (hL : lostMass B ν γ TM acut ≤ L) :
    FB B ν γ c ≤ ∑ T ∈ range (TM + 1), max 0 ((T : ℝ) - c) * D T + L := by
  have hsplit : FB B ν γ c =
      expect B ν γ (fun w => if Kept B TM acut w then max 0 ((tauN B w : ℝ) - c) else 0) +
      expect B ν γ (fun w => if Kept B TM acut w then 0 else max 0 ((tauN B w : ℝ) - c)) := by
    rw [← expect_add]
    refine expect_congr_fun fun w _ => ?_
    split_ifs <;> simp
  rw [hsplit, expect_kept_eq_sum B ν γ TM acut (fun T => max 0 ((T : ℝ) - c))]
  have h1 : ∑ T ∈ range (TM + 1), lawKept B ν γ TM acut T * max 0 ((T : ℝ) - c) ≤
      ∑ T ∈ range (TM + 1), max 0 ((T : ℝ) - c) * D T := by
    refine sum_le_sum fun T hT => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hD T (Nat.lt_succ_iff.1 (mem_range.1 hT)))
      (le_max_left _ _)
  have h2 : expect B ν γ (fun w => if Kept B TM acut w then 0 else max 0 ((tauN B w : ℝ) - c))
      ≤ lostMass B ν γ TM acut := by
    refine expect_mono hν fun w _ => ?_
    split_ifs
    · exact le_rfl
    · exact max_le (tauN_real_nonneg B w) (by linarith)
  linarith

/-- **`FB` bound, lower-tail form** (Lean checker's `fbUp`): uses
`(τ - c)^+ = τ - c + (c - τ)^+`; a path lost by the size cut has `τ ≥ TM + 1 ≥ c`, and a path
lost by an exponent cut contributes `(c - τ)^+ ≤ c`. For `0 ≤ c ≤ TM + 1`, `EB ≥ E[τ_B]`,
`D T ≥ P(τ_B = T, kept)` (`T ≤ TM`), `P ≥ P(∃ q ∈ B, v q > acut q)`:
`FB(c) ≤ EB - c + Σ_{T ≤ TM} (c - T)^+ D[T] + c · P`. -/
theorem FB_le_lowerTail (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (TM : ℕ) (hcTM : c ≤ (TM : ℝ) + 1) (acut : ℕ → ℕ) (EB : ℝ) (hEB : meanTau B ν γ ≤ EB)
    (D : ℕ → ℝ) (hD : ∀ T ≤ TM, lawKept B ν γ TM acut T ≤ D T) (P : ℝ)
    (hP : expLostProb B ν γ acut ≤ P) :
    FB B ν γ c ≤ EB - c + ∑ T ∈ range (TM + 1), max 0 (c - (T : ℝ)) * D T + c * P := by
  have hsplit : FB B ν γ c = meanTau B ν γ - c +
      (expect B ν γ (fun w => if Kept B TM acut w then max 0 (c - (tauN B w : ℝ)) else 0) +
       expect B ν γ (fun w => if Kept B TM acut w then 0 else max 0 (c - (tauN B w : ℝ)))) := by
    unfold FB meanTau
    rw [← expect_add, ← expect_const B ν γ c, ← expect_sub, ← expect_add]
    refine expect_congr_fun fun w _ => ?_
    rw [expect_const]
    have e : max 0 ((tauN B w : ℝ) - c) = ((tauN B w : ℝ) - c) + max 0 (c - (tauN B w : ℝ)) := by
      rcases le_total c (tauN B w : ℝ) with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
        ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
        ring
    rw [e]
    split_ifs <;> simp
  rw [hsplit, expect_kept_eq_sum B ν γ TM acut (fun T => max 0 (c - (T : ℝ)))]
  have h1 : ∑ T ∈ range (TM + 1), lawKept B ν γ TM acut T * max 0 (c - (T : ℝ)) ≤
      ∑ T ∈ range (TM + 1), max 0 (c - (T : ℝ)) * D T := by
    refine sum_le_sum fun T hT => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hD T (Nat.lt_succ_iff.1 (mem_range.1 hT)))
      (le_max_left _ _)
  have h2 : expect B ν γ (fun w => if Kept B TM acut w then 0 else max 0 (c - (tauN B w : ℝ)))
      ≤ c * expLostProb B ν γ acut := by
    unfold expLostProb
    rw [← expect_const_mul]
    refine expect_mono hν fun w _ => ?_
    by_cases hK : Kept B TM acut w
    · rw [ite_eq_left hK]
      split_ifs <;> simp [hc]
    · rw [ite_eq_right hK]
      unfold Kept at hK
      rw [not_and_or] at hK
      rcases hK with hK | hK
      · have : (TM : ℝ) + 1 ≤ (tauN B w : ℝ) := by exact_mod_cast (Nat.lt_of_not_le hK)
        rw [max_eq_left (by linarith)]
        split_ifs <;> simp [hc]
      · simp only [not_forall, not_le, exists_prop] at hK
        rw [ite_eq_left hK, mul_one]
        exact max_le hc (by linarith [tauN_real_nonneg B w])
  have h3 : c * expLostProb B ν γ acut ≤ c * P := mul_le_mul_of_nonneg_left hP hc
  linarith

/-! ### Suffix sums (`rigcert.c`) -/

/-- `S0[j] = Σ_{j ≤ T ≤ TM} D[T]`. -/
def sufS0 (D : ℕ → ℝ) (TM j : ℕ) : ℝ := ∑ T ∈ Ico j (TM + 1), D T

/-- `SS[j] = Σ_{j ≤ i ≤ TM} S0[i]`. -/
def sufSS (D : ℕ → ℝ) (TM j : ℕ) : ℝ := ∑ i ∈ Ico j (TM + 1), sufS0 D TM i

theorem sufS0_eq (D : ℕ → ℝ) (TM : ℕ) {j : ℕ} (hj : j ≤ TM) :
    sufS0 D TM j = D j + sufS0 D TM (j + 1) := by
  unfold sufS0
  rw [sum_eq_sum_Ico_succ_bot (by omega)]

theorem sufS0_of_lt (D : ℕ → ℝ) {TM j : ℕ} (hj : TM < j) : sufS0 D TM j = 0 := by
  unfold sufS0
  rw [Ico_eq_empty (by omega), sum_empty]

theorem sufSS_eq (D : ℕ → ℝ) (TM : ℕ) {j : ℕ} (hj : j ≤ TM) :
    sufSS D TM j = sufS0 D TM j + sufSS D TM (j + 1) := by
  unfold sufSS
  rw [sum_eq_sum_Ico_succ_bot (by omega)]

theorem sufSS_of_lt (D : ℕ → ℝ) {TM j : ℕ} (hj : TM < j) : sufSS D TM j = 0 := by
  unfold sufSS
  rw [Ico_eq_empty (by omega), sum_empty]

/-- `Σ_{a ≤ i < b} Σ_{i ≤ T < b} D[T] = Σ_{a ≤ T < b} (T - a + 1) D[T]`. -/
theorem sum_Ico_sum_Ico (D : ℕ → ℝ) (a b : ℕ) :
    ∑ i ∈ Ico a b, ∑ T ∈ Ico i b, D T = ∑ T ∈ Ico a b, ((T : ℝ) - a + 1) * D T := by
  induction b with
  | zero => simp
  | succ b ih =>
    by_cases hab : a ≤ b
    · have h1 : ∀ i ∈ Ico a (b + 1), ∑ T ∈ Ico i (b + 1), D T = ∑ T ∈ Ico i b, D T + D b :=
        fun i hi => sum_Ico_succ_top (Nat.lt_succ_iff.1 (mem_Ico.1 hi).2) D
      rw [sum_congr rfl h1, sum_add_distrib, sum_Ico_succ_top hab, Ico_self, sum_empty, add_zero,
        ih, sum_const, Nat.card_Ico, sum_Ico_succ_top hab, nsmul_eq_mul]
      have : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) - a + 1 := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [this]
    · rw [Ico_eq_empty (by omega), sum_empty, sum_empty]

/-- **Suffix-sum formula** (`rigcert.c`'s `FBup`): for an integer `k` with `k - 1 ≤ c ≤ k`
(rigcert takes `k = ⌊c⌋ + 1`),
`Σ_{T ≤ TM} (T - c)^+ D[T] = SS[k+1] + (k - c) S0[k]`. -/
theorem sum_hinge_eq_suffix (D : ℕ → ℝ) (TM : ℕ) {c : ℝ} {k : ℕ} (hk1 : (k : ℝ) - 1 ≤ c)
    (hk2 : c ≤ k) :
    ∑ T ∈ range (TM + 1), max 0 ((T : ℝ) - c) * D T =
      sufSS D TM (k + 1) + ((k : ℝ) - c) * sufS0 D TM k := by
  have hfilt : ∑ T ∈ range (TM + 1), max 0 ((T : ℝ) - c) * D T =
      ∑ T ∈ Ico k (TM + 1), ((T : ℝ) - c) * D T := by
    have e : ∀ T ∈ range (TM + 1), max 0 ((T : ℝ) - c) * D T =
        if k ≤ T then ((T : ℝ) - c) * D T else 0 := by
      intro T _
      split_ifs with h
      · have : (k : ℝ) ≤ T := by exact_mod_cast h
        rw [max_eq_right (by linarith)]
      · have : (T : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.lt_of_not_le h)
        rw [max_eq_left (by linarith), zero_mul]
    rw [sum_congr rfl e, ← sum_filter]
    congr 1
    ext T
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hfilt]
  have hsplit : ∑ T ∈ Ico k (TM + 1), ((T : ℝ) - c) * D T =
      ∑ T ∈ Ico k (TM + 1), ((T : ℝ) - k) * D T + ((k : ℝ) - c) * sufS0 D TM k := by
    unfold sufS0
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun T _ => by ring
  rw [hsplit]
  congr 1
  unfold sufSS sufS0
  rw [sum_Ico_sum_Ico]
  by_cases hk : k ≤ TM
  · rw [sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [sub_self, zero_mul, zero_add]
    refine sum_congr rfl fun T _ => ?_
    push_cast
    ring
  · rw [Ico_eq_empty (by omega), Ico_eq_empty (by omega), sum_empty, sum_empty]

/-! ### Prefix sums (Lean checker) -/

/-- `P0[j] = Σ_{T ≤ j} D[T]`. -/
def preS0 (D : ℕ → ℝ) (j : ℕ) : ℝ := ∑ T ∈ range (j + 1), D T

theorem preS0_succ (D : ℕ → ℝ) (j : ℕ) : preS0 D (j + 1) = preS0 D j + D (j + 1) := by
  unfold preS0
  rw [sum_range_succ]

/-- `Σ_{T ≤ k} (k - T) D[T] = Σ_{i < k} P0[i]`. -/
theorem sum_range_sub_mul_eq (D : ℕ → ℝ) (k : ℕ) :
    ∑ T ∈ range (k + 1), ((k : ℝ) - T) * D T = ∑ i ∈ range k, preS0 D i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ (fun i => preS0 D i) k, ← ih,
      sum_range_succ (fun T => (((k + 1 : ℕ) : ℝ) - T) * D T) (k + 1)]
    unfold preS0
    push_cast
    rw [sub_self, zero_mul, add_zero, ← sum_add_distrib]
    exact sum_congr rfl fun T _ => by ring

/-- **Prefix-sum formula** (checker's `fbTable`/`fbUp`): for `k = ⌊c⌋ ≤ TM`
(`k ≤ c < k + 1`), `Σ_{T ≤ TM} (c - T)^+ D[T] = Σ_{i < k} P0[i] + (c - k) P0[k]`. -/
theorem sum_lowerHinge_eq_prefix (D : ℕ → ℝ) (TM : ℕ) {c : ℝ} {k : ℕ} (hk1 : (k : ℝ) ≤ c)
    (hk2 : c < k + 1) (hkTM : k ≤ TM) :
    ∑ T ∈ range (TM + 1), max 0 (c - (T : ℝ)) * D T =
      ∑ i ∈ range k, preS0 D i + (c - k) * preS0 D k := by
  have hpos : ∀ T ∈ range (k + 1), max 0 (c - (T : ℝ)) * D T = (c - (T : ℝ)) * D T := by
    intro T hT
    have : (T : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hT)
    rw [max_eq_right (by linarith)]
  have hfilt : ∑ T ∈ range (TM + 1), max 0 (c - (T : ℝ)) * D T =
      ∑ T ∈ range (k + 1), (c - (T : ℝ)) * D T := by
    have hsub := sum_subset (f := fun T : ℕ => max 0 (c - (T : ℝ)) * D T)
      (range_mono (by omega : k + 1 ≤ TM + 1)) (fun T _ hnT => by
        have h1 : k + 1 ≤ T := by simpa using hnT
        have : (k : ℝ) + 1 ≤ T := by exact_mod_cast h1
        rw [max_eq_left (by linarith), zero_mul])
    rw [← hsub]
    exact sum_congr rfl hpos
  rw [hfilt, ← sum_range_sub_mul_eq]
  unfold preS0
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun T _ => by ring

/-! ### Combined forms with rounded inputs (for the code-level proof) -/

/-- **`G` from rounded inputs, `FB` case** (`rigcert.c`'s `Gup` with `u < t`, the checker's
`gUp`): if `α ≤ α'`, `0 < α'`, `u ≤ u'`, `c ≤ 1 + (t - u')/α'` (i.e. `c` rounded **down**) and
`FB(c) ≤ F`, then `G(α, u) ≤ α' · F`. -/
theorem GB_le_of_bounds (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (t : ℝ) {α α' u u' c F : ℝ}
    (hα : α ≤ α') (hα' : 0 < α') (hu : u ≤ u') (hc : c ≤ 1 + (t - u') / α')
    (hF : FB B ν γ c ≤ F) : GB B ν γ t α u ≤ α' * F := by
  calc GB B ν γ t α u ≤ GB B ν γ t α' u' := GB_mono hν γ t hα hu
    _ = α' * FB B ν γ (1 + (t - u') / α') := GB_eq_mul_FB γ hα' t u'
    _ ≤ α' * FB B ν γ c := mul_le_mul_of_nonneg_left (FB_antitone hν γ hc) hα'.le
    _ ≤ α' * F := mul_le_mul_of_nonneg_left hF hα'.le

/-- **`G` from rounded inputs, linear case** (`rigcert.c`'s `Gup` with `u ≥ t`): if `α ≤ α'`,
`0 ≤ α'`, `u ≤ u'`, `t ≤ u'` and `E[τ_B] ≤ EB`, then `G(α, u) ≤ (u' - t) + (EB - 1) α'`. -/
theorem GB_le_of_ge_bounds (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {t α α' u u' EB : ℝ}
    (hα : α ≤ α') (hα' : 0 ≤ α') (hu : u ≤ u') (htu : t ≤ u') (hEB : meanTau B ν γ ≤ EB) :
    GB B ν γ t α u ≤ (u' - t) + (EB - 1) * α' := by
  calc GB B ν γ t α u ≤ GB B ν γ t α' u' := GB_mono hν γ t hα hu
    _ = u' - t + (meanTau B ν γ - 1) * α' := GB_eq_of_le γ hα' htu
    _ ≤ (u' - t) + (EB - 1) * α' := by nlinarith

/-- `FB` via **suffix sums** (`rigcert.c`'s `FBup`, `c ≥ 1`, `k = ⌊c⌋ + 1`): for an integer `k`
with `k - 1 ≤ c ≤ k`, `c ≥ 0`, `D ≥ P(τ_B = ·, kept)` on `[0, TM]`, `L ≥ E[τ_B; lost]`:
`FB(c) ≤ SS[k+1] + (k - c) S0[k] + L`. (For `k > TM` both sums vanish: `FBup = tailB`.) -/
theorem FB_le_suffix (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (TM : ℕ) (acut : ℕ → ℕ) (D : ℕ → ℝ) (hD : ∀ T ≤ TM, lawKept B ν γ TM acut T ≤ D T)
    (L : ℝ) (hL : lostMass B ν γ TM acut ≤ L) {k : ℕ} (hk1 : (k : ℝ) - 1 ≤ c) (hk2 : c ≤ k) :
    FB B ν γ c ≤ sufSS D TM (k + 1) + ((k : ℝ) - c) * sufS0 D TM k + L := by
  have h := FB_le_kept hν γ hc TM acut D hD L hL
  rwa [sum_hinge_eq_suffix D TM hk1 hk2] at h

/-- `FB` via **prefix sums** (the Lean checker's `fbUp`): for `k = ⌊c⌋ ≤ TM` (`k ≤ c < k + 1`),
`c ≥ 0`, `EB ≥ E[τ_B]`, `D ≥ P(τ_B = ·, kept)` on `[0, TM]`, `P ≥ P(∃ q, v_q > acut q)`:
`FB(c) ≤ EB - c + (Σ_{i < k} P0[i] + (c - k) P0[k]) + c P`. -/
theorem FB_le_prefix (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c)
    (TM : ℕ) (acut : ℕ → ℕ) (EB : ℝ) (hEB : meanTau B ν γ ≤ EB) (D : ℕ → ℝ)
    (hD : ∀ T ≤ TM, lawKept B ν γ TM acut T ≤ D T) (P : ℝ) (hP : expLostProb B ν γ acut ≤ P)
    {k : ℕ} (hk1 : (k : ℝ) ≤ c) (hk2 : c < k + 1) (hkTM : k ≤ TM) :
    FB B ν γ c ≤ EB - c + (∑ i ∈ range k, preS0 D i + (c - k) * preS0 D k) + c * P := by
  have hcTM : c ≤ (TM : ℝ) + 1 := by
    have : (k : ℝ) ≤ TM := by exact_mod_cast hkTM
    linarith
  have h := FB_le_lowerTail hν γ hc TM hcTM acut EB hEB D hD P hP
  rwa [sum_lowerHinge_eq_prefix D TM hk1 hk2 hkTM] at h

/-! ### Forms matching the landed `CheckerImpl` (`fbUp`'s fallback, aggregated linear leaves) -/

/-- `FB(c) ≤ E[τ_B]` for `c ≥ 0` (since `(τ_B - c)^+ ≤ τ_B`). -/
theorem FB_le_meanTau (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {c : ℝ} (hc : 0 ≤ c) :
    FB B ν γ c ≤ meanTau B ν γ :=
  expect_mono hν fun w _ => max_le (tauN_real_nonneg B w) (by linarith)

/-- `fbUp`'s fallback branch (`⌊c⌋` beyond the prefix table): `FB(c) ≤ EB` for `c ≥ 0`,
`E[τ_B] ≤ EB`. -/
theorem FB_le_of_meanTau_le (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {c EB : ℝ}
    (hc : 0 ≤ c) (hEB : meanTau B ν γ ≤ EB) : FB B ν γ c ≤ EB :=
  (FB_le_meanTau hν γ hc).trans hEB

/-- **Aggregated linear leaves** (`CheckerImpl.comparisonCost`'s `lin1 + lin2`, and `remlin`):
for weights `w ≥ 0`, slopes `α ≥ 0` and values `u ≥ t` on a finite index set,
`Σ w G(α, u) ≤ Σ w (u - t) + (EB - 1) Σ w α` whenever `E[τ_B] ≤ EB`. -/
theorem sum_GB_linear_le (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {ι : Type*}
    (S : Finset ι) (w α u : ι → ℝ) {t EB : ℝ} (hw : ∀ i ∈ S, 0 ≤ w i)
    (hα : ∀ i ∈ S, 0 ≤ α i) (hu : ∀ i ∈ S, t ≤ u i) (hEB : meanTau B ν γ ≤ EB) :
    ∑ i ∈ S, w i * GB B ν γ t (α i) (u i) ≤
      ∑ i ∈ S, w i * (u i - t) + (EB - 1) * ∑ i ∈ S, w i * α i := by
  calc ∑ i ∈ S, w i * GB B ν γ t (α i) (u i)
      ≤ ∑ i ∈ S, w i * ((u i - t) + (EB - 1) * α i) :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (GB_le_of_ge_bounds hν γ le_rfl (hα i hi) le_rfl (hu i hi) hEB) (hw i hi)
    _ = ∑ i ∈ S, w i * (u i - t) + (EB - 1) * ∑ i ∈ S, w i * α i := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring

end MinModulus.CheckerMath
