import MinModulus.Checker2Sound.StatesH

/-!
# `Checker2Sound.StatesTauS` (agent L2-C): the weighted `τ_s` state (`TauSValid_init`, `TauSValid_add`)

STATUS: complete, no `sorry` (agent L2-C, lean2 stage 2). Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

The weighted law `W[T] ≥ 2^62·T·P(τ_S = T, kept)` (table `[0, TS]`, exponent cut `acut60`): one step
multiplies the old weighted mass `t·P(t)` by the weighted point mass `(a+1)·P(v = a)` (`weightByTau`),
since `T = t(a+1)`; the lost mass follows `TauLaw.lostMass_insert_le` with `P(t)·t = W[t]`.
-/

namespace MinModulus.Checker2Sound.C

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Main MinModulus.Smooth MinModulus.Checker2Sound

/-- The exponent cut of the τ_s and e laws is below every cap `N ≥ 64`. -/
theorem acut60_lt {q N : ℕ} (hq : 2 ≤ q) (hN : 64 ≤ N) : acut60 q < N := by
  have := acut60_le hq
  omega

/-- **(L2-C)** The empty weighted `τ_s` state. -/
theorem TauSValid_init (P : Params2) (hTS : 1 ≤ P.TS) : TauSValid P (TauSState.init P.TS) ∅ := by
  refine ⟨fun q hq => absurd hq (notMem_empty q), ?_, fun N _ T _ => ?_, fun N _ => ?_, ?_⟩
  · unfold TauSState.init
    simp only
    rw [size_set, size_zeros]
  · unfold TauSState.init
    simp only
    rw [lawKept_empty _ _ hTS, aget_set, size_zeros]
    by_cases hT : T = 1
    · subst hT
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, by omega⟩, pv_ONE2]
      norm_num
    · rw [ite_eq_right hT, mul_zero]
      exact pv_nonneg _
  · unfold TauSState.init
    simp only
    rw [lostMass_empty _ _ hTS, pv_zero]
  · unfold TauSState.init
    simp only
    rw [prod_empty, pv_ONE2]

/-- The product `∏_S (1 + ν/(q−1))` is nonnegative. -/
theorem prod_one_add_nonneg {P : Params2} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ q ≤ P.X) :
    0 ≤ ∏ r ∈ S, (1 + nu2 P r / ((r : ℝ) - 1)) := by
  refine prod_nonneg fun r hr => ?_
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (hS r hr).1.two_le
  have := (nu2_mem (hS r hr).1.two_le (hS r hr).2).1
  have : 0 ≤ nu2 P r / ((r : ℝ) - 1) := div_nonneg this (by linarith)
  linarith

/-- The mean step: `∏_{insert q S} (1 + ν/(q−1)) ≤ pv (mulUp E (facE1u q dn))`. -/
theorem mean_step {P : Params2} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ q ≤ P.X) {E : ℕ}
    (hE : ∏ r ∈ S, (1 + nu2 P r / ((r : ℝ) - 1)) ≤ pv E) {q : ℕ} (hq : q.Prime) (hqX : q ≤ P.X)
    (hqS : q ∉ S) :
    ∏ r ∈ insert q S, (1 + nu2 P r / ((r : ℝ) - 1)) ≤ pv (mulUp E (facE1u q (deltaN2 P q))) := by
  have hq2 := hq.two_le
  have hνq := nu2_mem hq2 hqX
  rw [prod_insert hqS]
  have h1 : 1 + nu2 P q / ((q : ℝ) - 1) ≤ pv (facE1u q (deltaN2 P q)) := by
    rw [nu2_eq_tiltN hqX]
    exact facE1u_ge hq2 (deltaN2_lt P q)
  have hq1 : (0 : ℝ) ≤ 1 + nu2 P q / ((q : ℝ) - 1) := by
    have hr2 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    have : 0 ≤ nu2 P q / ((q : ℝ) - 1) := div_nonneg hνq.1 (by linarith)
    linarith
  calc (1 + nu2 P q / ((q : ℝ) - 1)) * ∏ r ∈ S, (1 + nu2 P r / ((r : ℝ) - 1))
      ≤ pv (facE1u q (deltaN2 P q)) * pv E :=
        mul_le_mul h1 hE (prod_one_add_nonneg hS) (hq1.trans h1)
    _ = pv E * pv (facE1u q (deltaN2 P q)) := mul_comm _ _
    _ ≤ pv (mulUp E (facE1u q (deltaN2 P q))) := pv_mulUp _ _

/-- **(L2-C)** Adding a prime to the weighted `τ_s` DP (code: `dpRange`, `weightByTau`, `pmArr`,
`lostSumW`, `hArr`, `facE1u`; math: `TauLaw.lawKept_insert_le`, `lostMass_insert_le`,
`expect1_hA_le`, `expect1_add_one_le`, times the weight `T`). -/
theorem TauSValid_add (P : Params2) {st : TauSState} {S : Finset ℕ} (h : TauSValid P st S)
    {q : ℕ} (hq : q.Prime) (hqX : q ≤ P.X) (hqS : q ∉ S) :
    TauSValid P (st.add P.TS q (deltaN2 P q)) (insert q S) := by
  have hq2 := hq.two_le
  have hν : ∀ r ∈ S, 0 ≤ nu2 P r ∧ nu2 P r ≤ r := nu2_mem_of h.mem
  have hνq := nu2_mem hq2 hqX
  have hνi : ∀ r ∈ insert q S, 0 ≤ nu2 P r ∧ nu2 P r ≤ r := fun r hr => by
    rcases mem_insert.1 hr with rfl | hr
    · exact hνq
    · exact hν r hr
  set dn := deltaN2 P q with hdn
  set ac := acut60 q with hac
  set pm := pmArr q dn ac with hpm
  have hpms : pm.size = ac + 1 := pmArr_size q dn ac
  -- the weighted point masses
  have hw : ∀ N, 64 ≤ N → ∀ a ≤ ac,
      ((a : ℝ) + 1) * rho q (nu2 P q) N a ≤ pv (weightByTau pm)[a]! := by
    intro N hN a ha
    rw [weightByTau_get pm (by omega), pv_natMul]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [nu2_eq_tiltN hqX]
    exact rho_le_pmArr hq2 (two_deltaN2_le P q) ha (by have := acut60_lt hq2 hN; omega)
  refine ⟨fun r hr => ?_, ?_, fun N hN T hT => ?_, fun N hN => ?_, ?_⟩
  · rcases mem_insert.1 hr with rfl | hr
    · exact ⟨hq, hqX⟩
    · exact h.mem r hr
  · show (dpRange (zeros (P.TS + 1)) st.W P.TS (weightByTau pm) 0 (ac + 1)).size = P.TS + 1
    rw [dpRange_zeros_size]
  · -- the weighted law
    show (T : ℝ) * lawKept (insert q S) (nu2 P) (fun _ => N) P.TS acut60 T ≤
      pv (dpRange (zeros (P.TS + 1)) st.W P.TS (weightByTau pm) 0 (ac + 1))[T]!
    rcases Nat.eq_zero_or_pos T with rfl | hT1
    · rw [Nat.cast_zero, zero_mul]
      exact pv_nonneg _
    have hD := pv_dpRange_ge (zeros (P.TS + 1)) st.W P.TS (weightByTau pm) 0 (ac + 1)
      (by rw [size_zeros]; omega) hT
    rw [aget_zeros, pv_zero, zero_add] at hD
    refine le_trans ?_ hD
    rw [lawKept_insert hqS (nu2 P) (fun _ => N) P.TS acut60 hT, mul_sum, range_eq_Ico,
      sum_eq_sum_Ico_succ_bot (by omega : 0 < P.TS + 1)]
    have h0 : (T : ℝ) * ∑ a ∈ range (acut60 q + 1), (if 0 * (a + 1) = T then
        lawKept S (nu2 P) (fun _ => N) P.TS acut60 0 * rho q (nu2 P q) N a else 0) = 0 := by
      rw [sum_eq_zero fun a _ => ite_eq_right (by omega), mul_zero]
    rw [h0, zero_add]
    refine sum_le_sum fun t ht => ?_
    have ht' : t ≤ P.TS := by have := (mem_Ico.1 ht).2; omega
    rw [mul_sum, range_eq_Ico]
    refine sum_le_sum fun a ha => ?_
    have ha' : a ≤ ac := by have := (mem_Ico.1 ha).2; omega
    split_ifs with htT
    · have e : (T : ℝ) * (lawKept S (nu2 P) (fun _ => N) P.TS acut60 t * rho q (nu2 P q) N a) =
          ((t : ℝ) * lawKept S (nu2 P) (fun _ => N) P.TS acut60 t) *
            (((a : ℝ) + 1) * rho q (nu2 P q) N a) := by
        rw [← htT]
        push_cast
        ring
      rw [e]
      have h1 := h.law N hN t ht'
      have h2 := hw N hN a ha'
      have h1' : 0 ≤ (t : ℝ) * lawKept S (nu2 P) (fun _ => N) P.TS acut60 t :=
        mul_nonneg (Nat.cast_nonneg t) (lawKept_nonneg hν _ _ _ _)
      have h2' : 0 ≤ ((a : ℝ) + 1) * rho q (nu2 P q) N a :=
        mul_nonneg (by positivity) (rho_nonneg hνq.1 hνq.2 _ _)
      exact mul_le_mul h1 h2 h2' (h1'.trans h1)
    · rw [mul_zero]
  · -- the lost mass
    show lostMass (insert q S) (nu2 P) (fun _ => N) P.TS acut60 ≤
      pv (mulUp st.lost (facE1u q dn) + lostSumW st.W P.TS ac (hArr q dn (ac + 1)))
    have hlost := lostMass_insert_le hqS hνi (fun _ => N) P.TS acut60 (pv st.lost)
      (pv (facE1u q dn)) (fun t => pv st.W[t]! / t) (fun A => pv (hArr q dn (ac + 1))[A]!)
      (h.lost N hN) (fun t ht => by
        rcases Nat.eq_zero_or_pos t with rfl | ht0
        · rw [lawKept_zero, Nat.cast_zero, div_zero]
        · have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
          rw [le_div_iff₀ ht0', mul_comm]
          exact h.law N hN t ht)
      (by rw [nu2_eq_tiltN hqX]; exact expect1_add_one_le_facE1u hq2 (two_deltaN2_le P q) N)
      (fun t ht1 htT => by
        have hA1 := one_le_lostThr (ac := acut60 q) ht1 htT
        have hA2 : lostThr P.TS (acut60 q) t ≤ ac + 1 := min_le_right _ _
        rw [hArr_get q dn (ac + 1) hA2, nu2_eq_tiltN hqX]
        exact hMass_le_hUp hq2 (two_deltaN2_le P q) hA1 N)
    refine hlost.trans ?_
    rw [pv_add, lostSumW_eq, pv_sum]
    refine add_le_add (pv_mulUp _ _) ?_
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < P.TS + 1), Nat.cast_zero, mul_zero,
      zero_mul, zero_add]
    refine sum_le_sum fun t ht => ?_
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Ico.1 ht).1
    rw [div_mul_cancel₀ _ ht0.ne']
    exact pv_mulUp _ _
  · exact mean_step h.mem h.mean hq hqX hqS

end MinModulus.Checker2Sound.C
