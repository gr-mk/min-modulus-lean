import MinModulus.Checker2Sound.Defs
import MinModulus.Checker2Math.SplitLawTau
import MinModulus.CheckerMath.ImplBridge
import MinModulus.CheckerSound.TauDPArray

/-!
# `Checker2Sound.SplitCode`: the code of the τ-split (`Checker2Impl/TauSplit.lean`)

Owner: L2-B (lean2 stage 2). Namespace `MinModulus.Checker2Sound.B`.

* P-value arithmetic: `pv_mulUp_ge`, `pv_sub_ge`, `pv_add`, `pv_ONE2`, `pv_cdiv_ge`;
* the schedule: `delta2_nonneg`, `delta2_le_half`, `delta2_of_le`, `one_le_nu2`, `nu2_le_two`,
  `nu2_mem` (`0 ≤ ν_q ≤ q` for every `q ≥ 2`, primes or not);
* `suffixTablesW_get` (**the array spec**): for `1 ≤ k ≤ TS`,
  `SW[k] = Σ_{k ≤ T ≤ TS} W[T]`, `SV[k] = Σ_{k ≤ T ≤ TS} ⌊2^20 W[T]/T⌋`;
* `gsUp_sound`: `E[(τ_S − y)⁺] ≤ pv (gsUp (st.freeze TS) yP)` for `y = pv yP`, a valid weighted
  `τ_S` state, caps `N ≥ 64`;
* `splitVal_ge`: `pv (splitVal tb el NN XP) ≥ pv E·pv lost + Σ_{e ≤ NN} pv W[e]·pv (gsUp tb (XP >>> e))`;
* `pv_splitThreshold_le`: the threshold is a lower bound of `c1 + t(p − 1)` at every `p ≥ B` of a
  block (`B = p`, or `m ≤ B`);
* `splitCost_ge`: `pv (splitCost …) ≥ pv (splitVal …)·10^9/((B − 1)(10^9 − dn))`.
-/

namespace MinModulus.Checker2Sound.B

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Checker2Math.B MinModulus.Main MinModulus.Smooth

/-! ### P-values -/

theorem ONE2_real : (ONE2 : ℝ) = 2 ^ 62 := by rw [ONE2_eq, ONE_real]

theorem pv_nonneg (x : ℕ) : 0 ≤ pv x := by unfold pv; positivity

theorem pv_add (a b : ℕ) : pv (a + b) = pv a + pv b := by
  unfold pv
  push_cast
  ring

theorem pv_sub_ge (a b : ℕ) : pv a - pv b ≤ pv (a - b) := by
  unfold pv
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h, sub_div]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    have h2 : (a : ℝ) / 2 ^ 62 - (b : ℝ) / 2 ^ 62 ≤ 0 := by
      rw [← sub_div]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    simpa using h2

theorem pv_ONE2 : pv ONE2 = 1 := by
  unfold pv
  rw [ONE2_real]
  norm_num

theorem pv_mulUp_ge (x y : ℕ) : pv x * pv y ≤ pv (mulUp x y) := by
  have h := mulUp_ge x y
  rw [ONE_real] at h
  exact h

theorem pv_cdiv_ge (a : ℕ) {b : ℕ} (hb : 0 < b) : pv a / b ≤ pv (cdiv a b) := by
  unfold pv
  have h := cdiv_ge (a := a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem pv_mono {a b : ℕ} (h : a ≤ b) : pv a ≤ pv b := by
  unfold pv
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  exact div_le_div_of_nonneg_right this (by positivity)

/-! ### The schedule `δ` and the tilts -/

theorem DDEN_real : (DDEN : ℝ) = 10 ^ 9 := by
  unfold DDEN
  norm_num

theorem delta2_apply (P : Params2) (q : ℕ) :
    delta2 P q = ((deltaCert2 P q).1 : ℝ) / ((deltaCert2 P q).2 : ℝ) :=
  deltaPairR_apply _ q

theorem delta2_of_le (P : Params2) {q : ℕ} (hq : q ≤ P.X) :
    delta2 P q = (deltaN2 P q : ℝ) / DDEN := by
  rw [delta2_apply]
  unfold deltaCert2
  rw [ite_eq_right (by omega)]

theorem delta2_nonneg (P : Params2) (q : ℕ) : 0 ≤ delta2 P q := by
  rw [delta2_apply]
  positivity

theorem delta2_le_half (P : Params2) (q : ℕ) : delta2 P q ≤ 1 / 2 := by
  rw [delta2_apply]
  unfold deltaCert2
  split_ifs
  · norm_num
  · have h := deltaN2_le P q
    have h' : (deltaN2 P q : ℝ) ≤ 450000000 := by
      have : (DNMAX2 : ℝ) = 450000000 := by unfold DNMAX2; norm_num
      exact_mod_cast (show deltaN2 P q ≤ 450000000 from h)
    simp only
    rw [DDEN_real, div_le_iff₀ (by norm_num)]
    linarith

theorem delta2_lt_one (P : Params2) (q : ℕ) : delta2 P q < 1 :=
  (delta2_le_half P q).trans_lt (by norm_num)

theorem one_le_nu2 (P : Params2) (q : ℕ) : 1 ≤ nu2 P q := by
  unfold nu2 tilt
  have h0 := delta2_nonneg P q
  have h1 := delta2_lt_one P q
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem nu2_le_two (P : Params2) (q : ℕ) : nu2 P q ≤ 2 := by
  unfold nu2 tilt
  have h1 := delta2_le_half P q
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- **Admissible tilts**: `0 ≤ ν_q ≤ q` for every `q ≥ 2` (primes or not). -/
theorem nu2_mem (P : Params2) {q : ℕ} (hq : 2 ≤ q) : 0 ≤ nu2 P q ∧ nu2 P q ≤ q := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  exact ⟨le_trans zero_le_one (one_le_nu2 P q), (nu2_le_two P q).trans hq'⟩

theorem deltaN2_lt_DDEN (P : Params2) (q : ℕ) : deltaN2 P q < DDEN :=
  lt_of_le_of_lt (deltaN2_le P q) (by decide)

/-! ### `suffixTablesW` -/

theorem suffixTablesW_go_get (W : Array ℕ) :
    ∀ (f T aw av : ℕ) (SW SV : Array ℕ), f ≤ T → T < SW.size → T < SV.size → ∀ k,
      (suffixTablesW.go W T aw av SW SV f).1[k]! =
          (if T - f < k ∧ k ≤ T then aw + ∑ i ∈ Ico k (T + 1), W[i]! else SW[k]!) ∧
      (suffixTablesW.go W T aw av SW SV f).2[k]! =
          (if T - f < k ∧ k ≤ T then av + ∑ i ∈ Ico k (T + 1), (W[i]! <<< 20) / i else SV[k]!) := by
  intro f
  induction f with
  | zero =>
    intro T aw av SW SV _ _ _ k
    have : ¬ (T - 0 < k ∧ k ≤ T) := by omega
    simp only [suffixTablesW.go, this, ↓reduceIte, and_self]
  | succ f ih =>
    intro T aw av SW SV hf hSW hSV k
    rw [suffixTablesW.go]
    have hSW' : T - 1 < (SW.set! T (aw + W[T]!)).size := by
      rw [MinModulus.CheckerSound.B.size_set!]; omega
    have hSV' : T - 1 < (SV.set! T (av + (W[T]! <<< 20) / T)).size := by
      rw [MinModulus.CheckerSound.B.size_set!]; omega
    obtain ⟨h1, h2⟩ := ih (T - 1) (aw + W[T]!) (av + (W[T]! <<< 20) / T)
      (SW.set! T (aw + W[T]!)) (SV.set! T (av + (W[T]! <<< 20) / T)) (by omega) hSW' hSV' k
    rw [h1, h2, MinModulus.CheckerSound.B.getElem!_set!, MinModulus.CheckerSound.B.getElem!_set!]
    have hT1 : T - 1 + 1 = T := by omega
    by_cases hA : T - 1 - f < k ∧ k ≤ T - 1
    · have hB : T - (f + 1) < k ∧ k ≤ T := by omega
      rw [ite_eq_left hA, ite_eq_left hA, ite_eq_left hB, ite_eq_left hB, hT1,
        sum_Ico_succ_top (by omega : k ≤ T), sum_Ico_succ_top (by omega : k ≤ T)]
      constructor <;> ring
    · rw [ite_eq_right hA, ite_eq_right hA]
      by_cases hk : k = T
      · subst hk
        have hB : k - (f + 1) < k ∧ k ≤ k := by omega
        rw [ite_eq_left (show k = k ∧ k < SW.size from ⟨rfl, hSW⟩),
          ite_eq_left (show k = k ∧ k < SV.size from ⟨rfl, hSV⟩), ite_eq_left hB, ite_eq_left hB,
          Nat.Ico_succ_singleton, sum_singleton, sum_singleton]
        exact ⟨rfl, rfl⟩
      · have hB : ¬ (T - (f + 1) < k ∧ k ≤ T) := by omega
        have hne : ¬ (T = k ∧ T < SW.size) := fun h => hk h.1.symm
        have hne' : ¬ (T = k ∧ T < SV.size) := fun h => hk h.1.symm
        rw [ite_eq_right hne, ite_eq_right hne', ite_eq_right hB, ite_eq_right hB]
        exact ⟨rfl, rfl⟩

/-- **The suffix tables** of a weighted law: for `1 ≤ k ≤ TS`,
`SW[k] = Σ_{k ≤ T ≤ TS} W[T]` and `SV[k] = Σ_{k ≤ T ≤ TS} ⌊W[T]·2^20/T⌋`. -/
theorem suffixTablesW_get (W : Array ℕ) (TS : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ TS) :
    (suffixTablesW W TS).1[k]! = ∑ i ∈ Ico k (TS + 1), W[i]! ∧
      (suffixTablesW W TS).2[k]! = ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i := by
  unfold suffixTablesW
  have hs : TS < (zeros (TS + 2)).size := by simp [zeros]
  obtain ⟨h1, h2⟩ := suffixTablesW_go_get W TS TS 0 0 (zeros (TS + 2)) (zeros (TS + 2)) le_rfl
    hs hs k
  have hc : TS - TS < k ∧ k ≤ TS := by omega
  rw [h1, h2, ite_eq_left hc, ite_eq_left hc, zero_add, zero_add]
  exact ⟨rfl, rfl⟩

/-! ### `gsUp` -/

theorem freeze_SW (st : TauSState) (TS : ℕ) : (st.freeze TS).SW = (suffixTablesW st.W TS).1 := rfl
theorem freeze_SV (st : TauSState) (TS : ℕ) : (st.freeze TS).SV = (suffixTablesW st.W TS).2 := rfl
theorem freeze_E (st : TauSState) (TS : ℕ) : (st.freeze TS).E = st.E := rfl
theorem freeze_lost (st : TauSState) (TS : ℕ) : (st.freeze TS).lost = st.lost := rfl
theorem freeze_TS (st : TauSState) (TS : ℕ) : (st.freeze TS).TS = TS := rfl

/-- The tilts are admissible on a `τ_S`-set. -/
theorem nu2_mem_of_tauS (P : Params2) {st : TauSState} {S : Finset ℕ} (hS : TauSValid P st S) :
    ∀ q ∈ S, 0 ≤ nu2 P q ∧ nu2 P q ≤ q := fun q hq =>
  nu2_mem P (hS.mem q hq).1.two_le

/-- The tilts are admissible on an e-law set. -/
theorem nu2_mem_of_eLaw (P : Params2) {el : ELaw} {L : Finset ℕ} (hL : ELawValid P el L) :
    ∀ q ∈ L, 0 ≤ nu2 P q ∧ nu2 P q ≤ q := fun q hq =>
  nu2_mem P (by have := (hL.mem q hq).1; omega)

/-- `E[τ_S] ≤ pv E` for a valid `τ_S` state (every cap). -/
theorem meanTau_le_pv (P : Params2) {st : TauSState} {S : Finset ℕ} (hS : TauSValid P st S)
    (γ : ℕ → ℕ) : meanTau S (nu2 P) γ ≤ pv st.E :=
  (meanTau_le (fun q hq => (hS.mem q hq).1.one_lt) (fun q hq => (nu2_mem_of_tauS P hS q hq).1)
    γ).trans hS.mean

/-- `⌊yP/2^62⌋ ≤ pv yP < ⌊yP/2^62⌋ + 1`. -/
theorem div_ONE2_le_pv (yP : ℕ) : ((yP / ONE2 : ℕ) : ℝ) ≤ pv yP := by
  unfold pv
  rw [← ONE2_real]
  exact Nat.cast_div_le

theorem pv_lt_div_ONE2_succ (yP : ℕ) : pv yP < ((yP / ONE2 + 1 : ℕ) : ℝ) := by
  unfold pv
  have hO : 0 < ONE2 := by rw [ONE2_eq]; exact ONE_pos
  have h := Nat.lt_div_mul_add (a := yP) hO
  have h' : (yP : ℝ) < ((yP / ONE2 : ℕ) : ℝ) * ONE2 + ONE2 := by exact_mod_cast h
  have hO' : (0 : ℝ) < 2 ^ 62 := by positivity
  rw [div_lt_iff₀ hO', ← ONE2_real]
  push_cast
  linarith

theorem pv_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) : pv (∑ i ∈ s, f i) = ∑ i ∈ s, pv (f i) := by
  unfold pv
  push_cast
  rw [sum_div]

theorem pv_sub_of_le {a b : ℕ} (h : b ≤ a) : pv (a - b) = pv a - pv b := by
  unfold pv
  rw [Nat.cast_sub h, sub_div]

/-- The subtracted term of `gsUp`: `pv ((yP·SV[k]) >>> 82) ≤ y·Σ_{k ≤ T ≤ TS} pv W[T]/T`. -/
theorem pv_shift82_le (W : Array ℕ) (TS k yP : ℕ) :
    pv ((yP * ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i) >>> 82) ≤
      pv yP * ∑ T ∈ Ico k (TS + 1), pv W[T]! / T := by
  rw [Nat.shiftRight_eq_div_pow]
  have h1 : (((yP * ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i) / 2 ^ 82 : ℕ) : ℝ) ≤
      ((yP * ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i : ℕ) : ℝ) / 2 ^ 82 := by
    have := Nat.cast_div_le (α := ℝ) (m := yP * ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i)
      (n := 2 ^ 82)
    exact_mod_cast this
  have h2 : ((∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i : ℕ) : ℝ) ≤
      ∑ T ∈ Ico k (TS + 1), (W[T]! : ℝ) * 2 ^ 20 / T := by
    rw [Nat.cast_sum]
    refine sum_le_sum fun T _ => ?_
    rw [Nat.shiftLeft_eq]
    have := Nat.cast_div_le (α := ℝ) (m := W[T]! * 2 ^ 20) (n := T)
    exact_mod_cast this
  have hy : (0 : ℝ) ≤ yP := Nat.cast_nonneg yP
  have h3 : ((yP * ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i : ℕ) : ℝ) ≤
      (yP : ℝ) * ∑ T ∈ Ico k (TS + 1), (W[T]! : ℝ) * 2 ^ 20 / T := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left h2 hy
  unfold pv
  calc (((yP * ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i) / 2 ^ 82 : ℕ) : ℝ) / 2 ^ 62
      ≤ ((yP * ∑ i ∈ Ico k (TS + 1), (W[i]! <<< 20) / i : ℕ) : ℝ) / 2 ^ 82 / 2 ^ 62 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ (yP : ℝ) * (∑ T ∈ Ico k (TS + 1), (W[T]! : ℝ) * 2 ^ 20 / T) / 2 ^ 82 / 2 ^ 62 := by
        gcongr
    _ = (yP : ℝ) / 2 ^ 62 * ∑ T ∈ Ico k (TS + 1), (W[T]! : ℝ) / 2 ^ 62 / T := by
        rw [mul_sum, mul_sum, sum_div, sum_div]
        refine sum_congr rfl fun T _ => ?_
        ring

/-- **`gsUp` is sound**: for a valid weighted `τ_S` state and caps `N ≥ 64`,
`E[(τ_S − y)⁺] ≤ pv (gsUp (st.freeze TS) yP)` with `y = pv yP` (all three branches). -/
theorem gsUp_sound (P : Params2) {st : TauSState} {S : Finset ℕ} (hS : TauSValid P st S)
    {N : ℕ} (hN : 64 ≤ N) (yP : ℕ) :
    FB S (nu2 P) (fun _ => N) (pv yP) ≤ pv (gsUp (st.freeze P.TS) yP) := by
  have hν := nu2_mem_of_tauS P hS
  have hy0 : 0 ≤ pv yP := pv_nonneg yP
  unfold gsUp
  rw [freeze_E, freeze_TS, freeze_lost, freeze_SW, freeze_SV]
  dsimp only
  split_ifs with h1 h2
  · -- `y < 1`: `E[(τ_S − y)⁺] = E[τ_S] − y`
    have hy1 : pv yP ≤ 1 := by
      have : pv yP < 1 := by
        unfold pv
        rw [div_lt_one (by positivity), ← ONE2_real]
        exact_mod_cast h1
      linarith
    rw [FB_eq_of_le_one _ hy1]
    exact (sub_le_sub_right (meanTau_le_pv P hS _) _).trans (pv_sub_ge _ _)
  · -- `k > TS`: `y ≥ TS`, only the lost mass
    refine FB_le_lost_of_ge hν _ P.TS acut60 (pv st.lost) (hS.lost N hN) ?_
    have : P.TS ≤ yP / ONE2 := by omega
    exact le_trans (by exact_mod_cast this) (div_ONE2_le_pv yP)
  · -- `k ≤ TS`: the weighted suffix bound
    have h2' : yP / ONE2 + 1 ≤ P.TS := by omega
    obtain ⟨hSWk, hSVk⟩ := suffixTablesW_get st.W P.TS (k := yP / ONE2 + 1) (Nat.le_add_left 1 _) h2'
    rw [hSWk, hSVk]
    have hk1 : (((yP / ONE2 + 1 : ℕ) : ℝ)) - 1 ≤ pv yP := by
      push_cast
      linarith [div_ONE2_le_pv yP]
    have hFB := FB_le_weighted hν (fun _ => N) P.TS acut60 (fun T => pv st.W[T]!)
      (hS.law N hN) (pv st.lost) (hS.lost N hN) hy0 hk1 (pv_lt_div_ONE2_succ yP)
    refine hFB.trans ?_
    rw [pv_add]
    refine add_le_add ?_ le_rfl
    refine le_trans ?_ (pv_sub_ge _ _)
    have hsplit : ∑ T ∈ Ico (yP / ONE2 + 1) (P.TS + 1), (1 - pv yP / T) * pv st.W[T]! =
        pv (∑ i ∈ Ico (yP / ONE2 + 1) (P.TS + 1), st.W[i]!) -
          pv yP * ∑ T ∈ Ico (yP / ONE2 + 1) (P.TS + 1), pv st.W[T]! / T := by
      rw [pv_sum, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun T _ => ?_
      ring
    rw [hsplit]
    exact sub_le_sub_left (pv_shift82_le st.W P.TS (yP / ONE2 + 1) yP) _

/-! ### `splitVal` -/

theorem splitVal_go_eq (tb : TauSTab) (el : ELaw) (XP : ℕ) : ∀ (f e acc : ℕ),
    splitVal.go tb el XP e f acc = acc + ∑ i ∈ range f,
      (if el.W[e + i]! = 0 then 0 else mulUp el.W[e + i]! (gsUp tb (XP >>> (e + i)))) := by
  intro f
  induction f with
  | zero =>
    intro e acc
    simp [splitVal.go]
  | succ f ih =>
    intro e acc
    rw [splitVal.go, sum_range_succ']
    have hs : ∑ i ∈ range f, (if el.W[e + (i + 1)]! = 0 then 0 else
          mulUp el.W[e + (i + 1)]! (gsUp tb (XP >>> (e + (i + 1))))) =
        ∑ i ∈ range f, (if el.W[e + 1 + i]! = 0 then 0 else
          mulUp el.W[e + 1 + i]! (gsUp tb (XP >>> (e + 1 + i)))) :=
      sum_congr rfl fun i _ => by rw [show e + (i + 1) = e + 1 + i by omega]
    rw [hs]
    by_cases h : el.W[e]! = 0
    · simp only [h, beq_self_eq_true, ↓reduceIte, add_zero]
      rw [ih]
    · have hb : (el.W[e]! == 0) = false := by simpa using h
      simp only [hb, h, ↓reduceIte, add_zero, Bool.false_eq_true]
      rw [ih]
      ring

/-- **`splitVal` is an upper bound** of `pv E·pv lost + Σ_{e ≤ NN} pv W[e]·pv (gsUp tb (XP >>> e))`. -/
theorem splitVal_ge (tb : TauSTab) (el : ELaw) (NN XP : ℕ) :
    pv tb.E * pv el.lost + ∑ e ∈ range (NN + 1), pv el.W[e]! * pv (gsUp tb (XP >>> e)) ≤
      pv (splitVal tb el NN XP) := by
  unfold splitVal
  rw [splitVal_go_eq, pv_add, pv_sum]
  refine add_le_add (pv_mulUp_ge _ _) (sum_le_sum fun e _ => ?_)
  simp only [zero_add]
  split_ifs with h
  · rw [h]
    simp [pv]
  · exact pv_mulUp_ge _ _

/-- `pv (XP >>> e) ≤ pv XP / 2^e`. -/
theorem pv_shiftRight_le (XP e : ℕ) : pv (XP >>> e) ≤ pv XP / 2 ^ e := by
  rw [Nat.shiftRight_eq_div_pow]
  unfold pv
  have h := Nat.cast_div_le (α := ℝ) (m := XP) (n := 2 ^ e)
  push_cast at h
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right h (by positivity)

/-! ### `splitThreshold` and `splitCost` -/

/-- **The threshold is a lower bound**: at every `p ≥ B` of the block (`B = p`, or `m ≤ B`),
`pv (splitThreshold m B dn) ≤ [p < m](1 − 1/p) + (dn/10^9)(p − 1)`. -/
theorem pv_splitThreshold_le {m B p dn : ℕ} (hB1 : 1 ≤ B) (hBp : B ≤ p)
    (hBp' : B = p ∨ m ≤ B) :
    pv (splitThreshold m B dn) ≤
      (if p < m then 1 - 1 / (p : ℝ) else 0) + (dn : ℝ) / DDEN * ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hB1.trans hBp)
  unfold splitThreshold
  rw [pv_add]
  refine add_le_add ?_ ?_
  · split_ifs with h1 h2 h2
    · -- `B < m`, hence `B = p`
      have hBeq : B = p := by
        rcases hBp' with h | h
        · exact h
        · omega
      subst hBeq
      have hB0 : 0 < B := by omega
      have hc : pv ONE2 / B ≤ pv (cdiv ONE2 B) := pv_cdiv_ge ONE2 hB0
      rw [pv_ONE2] at hc
      by_cases hle : cdiv ONE2 B ≤ ONE2
      · rw [pv_sub_of_le hle, pv_ONE2]
        linarith
      · rw [Nat.sub_eq_zero_of_le (by omega)]
        have : (1 : ℝ) / B ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast hB1
        rw [show pv 0 = 0 by simp [pv]]
        linarith
    · exfalso
      rcases hBp' with h | h <;> omega
    · simp only [pv, Nat.cast_zero, zero_div]
      have : (1 : ℝ) / p ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hp1
      linarith
    · simp [pv]
  · have hB1' : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by rw [Nat.cast_sub hB1]; simp
    have hDD : (0 : ℝ) < DDEN := by exact_mod_cast DDEN_pos
    have h1 : pv (dn * (B - 1) * ONE2 / DDEN) ≤ pv (dn * (B - 1) * ONE2) / DDEN := by
      unfold pv
      have := Nat.cast_div_le (α := ℝ) (m := dn * (B - 1) * ONE2) (n := DDEN)
      calc ((dn * (B - 1) * ONE2 / DDEN : ℕ) : ℝ) / 2 ^ 62
          ≤ ((dn * (B - 1) * ONE2 : ℕ) : ℝ) / DDEN / 2 ^ 62 :=
            div_le_div_of_nonneg_right this (by positivity)
        _ = ((dn * (B - 1) * ONE2 : ℕ) : ℝ) / 2 ^ 62 / DDEN := by ring
    have h2 : pv (dn * (B - 1) * ONE2) = (dn : ℝ) * ((B : ℝ) - 1) := by
      unfold pv
      rw [Nat.cast_mul, Nat.cast_mul, hB1', ONE2_real]
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    have hBp'' : (B : ℝ) - 1 ≤ (p : ℝ) - 1 := by
      have : (B : ℝ) ≤ p := by exact_mod_cast hBp
      linarith
    have hdn0 : (0 : ℝ) ≤ dn := Nat.cast_nonneg dn
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBp'' hdn0) hDD.le

/-- **`splitCost`**: `pv (splitCost …) ≥ pv (splitVal …)·10^9/((B − 1)(10^9 − dn))`. -/
theorem splitCost_ge (m NN B dn : ℕ) (tb : TauSTab) (el : ELaw) (hB : 2 ≤ B) (hdn : dn < DDEN) :
    pv (splitVal tb el NN (splitThreshold m B dn)) * DDEN / (((B : ℝ) - 1) * ((DDEN : ℝ) - dn)) ≤
      pv (splitCost m NN B dn tb el) := by
  unfold splitCost
  have hb : 0 < (B - 1) * (DDEN - dn) := Nat.mul_pos (by omega) (by omega)
  refine le_trans (le_of_eq ?_) (pv_cdiv_ge _ hb)
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ B), Nat.cast_sub hdn.le]
  unfold pv
  push_cast
  ring

end MinModulus.Checker2Sound.B
