import MinModulus.Checker2Sound.StatesTauS
import MinModulus.Checker2Math.SplitLawE

/-!
# `Checker2Sound.StatesE` (agent L2-C): the weighted e-law (`ELawValid_init`, `ELawValid_add`)

STATUS: complete, no `sorry` (agent L2-C, lean2 stage 2). Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

The weighted law `W[e] ≥ 2^62·2^e·P(e, kept)` on `[0, NN]` with exponent cut `acut60`, and
`lost ≥ 2^62·E[2^e; ¬kept]`. Code: `ELaw.add` (`eOuter`/`eInner`, `weightByPow2`, `pmArr`, `e2Up`,
`h2Up`); math: L2-B's `Checker2Math.B.lawE_insert_le`, `lostE_insert_le`, `expect1_two_pow_le`,
`expect1_two_pow_ge_le` (module `Checker2Math/SplitLawE.lean`).
-/

namespace MinModulus.Checker2Sound.C

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Main MinModulus.Smooth MinModulus.Checker2Sound

/-- **(L2-C)** The empty weighted e-law. -/
theorem ELawValid_init (P : Params2) : ELawValid P (ELaw.init P.NN) ∅ := by
  refine ⟨fun q hq => absurd hq (notMem_empty q), ?_, fun N _ e _ => ?_, fun N _ => ?_⟩
  · unfold ELaw.init
    simp only
    rw [size_set, size_zeros]
  · unfold ELaw.init
    simp only
    rw [B.lawE_empty, aget_set, size_zeros]
    by_cases he : e = 0
    · subst he
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, by omega⟩, pv_ONE2]
      norm_num
    · rw [ite_eq_right he, mul_zero]
      exact pv_nonneg _
  · unfold ELaw.init
    simp only
    rw [B.lostE_empty, pv_zero]

/-- **(L2-C)** Adding a number `q ≥ 3` to the weighted e-law (code: `eOuter`, `eInner`,
`weightByPow2`, `pmArr`, `h2Up`, `e2Up`; math: the e-law recursion of L2-B). -/
theorem ELawValid_add (P : Params2) {el : ELaw} {L : Finset ℕ} (h : ELawValid P el L) {q : ℕ}
    (hq : 3 ≤ q) (hqX : q ≤ P.X) (hqL : q ∉ L) :
    ELawValid P (el.add P.NN q (deltaN2 P q)) (insert q L) := by
  have hq2 : 2 ≤ q := by omega
  have hνq := nu2_mem hq2 hqX
  have hνi : ∀ r ∈ insert q L, 0 ≤ nu2 P r ∧ nu2 P r ≤ r := fun r hr => by
    rcases mem_insert.1 hr with rfl | hr
    · exact hνq
    · exact nu2_mem (by have := (h.mem r hr).1; omega) (h.mem r hr).2
  set dn := deltaN2 P q with hdn
  set ac := acut60 q with hac
  set mu := weightByPow2 (pmArr q dn ac) with hmu
  have hmus : (pmArr q dn ac).size = ac + 1 := pmArr_size q dn ac
  -- the weighted point masses `2^a·ρ(a) ≤ pv mu[a]`
  have hℓ : ∀ N, 64 ≤ N → ∀ a ≤ acut60 q,
      (2 : ℝ) ^ a * rho q (nu2 P q) ((fun _ => N) q) a ≤ pv mu[a]! := by
    intro N hN a ha
    rw [hmu, weightByPow2_get (pmArr q dn ac) (by omega : a < (pmArr q dn ac).size),
      Nat.mul_comm (pmArr q dn ac)[a]! (2 ^ a), pv_natMul]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact rho_nu2_le_pmArr hq2 hqX ha (by have := acut60_lt hq2 hN; omega)
  have hD : ∀ N, 64 ≤ N → ∀ e ≤ P.NN,
      (2 : ℝ) ^ e * lawE L (nu2 P) (fun _ => N) P.NN acut60 e ≤ pv el.W[e]! :=
    fun N hN e he => h.law N hN e he
  have hW := eLawAdd_W el P.NN q dn
  refine ⟨fun r hr => ?_, hW.1, fun N hN j hj => ?_, fun N hN => ?_⟩
  · rcases mem_insert.1 hr with rfl | hr
    · exact ⟨hq, hqX⟩
    · exact h.mem r hr
  · -- the weighted law
    refine (B.lawE_insert_le hqL hνi (fun _ => N) P.NN acut60 (fun e => pv el.W[e]!)
      (fun a => pv mu[a]!) (hD N hN) (hℓ N hN) hj).trans ?_
    rw [hW.2 j hj, pv_sum]
    refine sum_le_sum fun e _ => ?_
    rw [pv_sum]
    refine sum_le_sum fun a _ => ?_
    rw [pv_ite]
    split_ifs
    · exact pv_mulUp _ _
    · exact le_rfl
  · -- the lost mass
    have hE2 : expect1 q (nu2 P q) ((fun _ => N) q) (fun a => (2 : ℝ) ^ a) ≤ pv (e2Up q dn) := by
      refine (B.expect1_two_pow_le hq hνq.1 N).trans ?_
      rw [nu2_eq_tiltN hqX]
      exact e2Up_ge hq (deltaN2_lt P q)
    have hH : expect1 q (nu2 P q) ((fun _ => N) q)
        (fun a => if acut60 q + 1 ≤ a then (2 : ℝ) ^ a else 0) ≤ pv (h2Up q dn (ac + 1)) := by
      refine (B.expect1_two_pow_ge_le hq hνq.1 (by omega) N).trans ?_
      rw [nu2_eq_tiltN hqX]
      exact h2Up_ge hq (deltaN2_lt P q) (ac + 1)
    refine (B.lostE_insert_le hqL hνi (fun _ => N) P.NN acut60 (pv el.lost) (pv (e2Up q dn))
      (pv (h2Up q dn (ac + 1))) (fun e => pv el.W[e]!) (fun a => pv mu[a]!) (h.lost N hN)
      (hD N hN) hE2 (hℓ N hN) hH).trans ?_
    rw [eLawAdd_lost, pv_add, pv_sum]
    refine add_le_add (pv_mulUp _ _) (sum_le_sum fun e _ => ?_)
    rw [pv_add, pv_sum, mul_add, mul_sum]
    refine add_le_add (sum_le_sum fun a _ => ?_) (pv_mulUp _ _)
    rw [pv_ite]
    split_ifs
    · exact pv_mulUp _ _
    · rw [mul_zero]

end MinModulus.Checker2Sound.C
