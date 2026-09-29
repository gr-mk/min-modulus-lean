import MinModulus.Checker2Sound.SplitCode
import MinModulus.CheckerMath.ComparisonBound

/-!
# `Checker2Sound.Split`: soundness of the τ-split cost (`splitCost_sound`)

Owner: L2-B (lean2 stage 2). Namespace `MinModulus.Checker2Sound.B`.

**`splitCost_sound`** (the statement of `Checker2Sound/Interfaces.lean`, verbatim): for a prime
`p ≤ X` and `B ≤ p` with `m ≤ 2B` (`B = p` per prime, or `B` = the block start with `m ≤ B`) and
the same δ at `B` and `p`, a valid weighted `τ_S` state and a valid weighted e-law for disjoint
`S`, `L` covering the primes below `p`:
`hingeLoss m δ p (fun _ => N) ≤ pv (splitCost m NN B dn (st.freeze TS) el)` for every cap `N`.

Proof:
1. caps `N ≥ 64` suffice (`CheckerMath.hingeLoss_le_of_forall_ge`, monotone coupling);
2. `hingeLoss = E[(τ(s) − X)⁺]/((p − 1)(1 − δ_p))` with `X = [p < m](1 − 1/p) + δ_p (p − 1)`
   (`Checker2Math.hingeLoss_eq_tauSplit`);
3. `E[(τ(s) − X)⁺] ≤ Σ_{e ≤ NN} 2^e P_L(e, kept)·E_S[(τ_S − X/2^e)⁺] + E[τ_S]·E_L[2^e; lost]`
   (`Checker2Math.B.expect_hinge_tauSplit_le`: marginalization to `S ∪ L`, domination
   `τ ≤ τ_S 2^e`, Fubini, kept/lost split of the e-law);
4. each term against the code: `2^e P(e, kept) ≤ pv W_e[e]` (`ELawValid`),
   `E_S[(τ_S − X/2^e)⁺] ≤ E_S[(τ_S − y_e)⁺] ≤ pv (gsUp tb (XP >>> e))` with
   `y_e = pv (XP >>> e) ≤ X/2^e` (`pv_splitThreshold_le`, `gsUp_sound`),
   `E[τ_S] ≤ pv E`, `E_L[2^e; lost] ≤ pv lost_e`; the sum is `≤ pv (splitVal …)` (`splitVal_ge`);
5. the division: `(B − 1)(10^9 − dn) ≤ (p − 1)(10^9 − dn)` and `splitCost_ge`.
-/

namespace MinModulus.Checker2Sound.B

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Checker2Math.B MinModulus.Main MinModulus.Smooth

/-- The numerator of the τ-split bound against the code, for caps `N ≥ 64`: with
`XP` a lower P-value of the threshold `X ≥ 0`,
`E_{PB}[(τ(s_{PB}) − X)⁺] ≤ pv (splitVal (st.freeze TS) el NN XP)`. -/
theorem expect_hinge_le_splitVal (P : Params2) {st : TauSState} {S : Finset ℕ}
    (hS : TauSValid P st S) {el : ELaw} {L : Finset ℕ} (hL : ELawValid P el L)
    (hSL : Disjoint S L) {PB : Finset ℕ} (hPB : ∀ q ∈ PB, q.Prime) (hsub : PB ⊆ S ∪ L)
    {N : ℕ} (hN : 64 ≤ N) {X : ℝ} (hX : 0 ≤ X) {XP : ℕ} (hXP : pv XP ≤ X) :
    expect PB (nu2 P) (fun _ => N) (fun v => max 0 (((smooth PB v).divisors.card : ℝ) - X)) ≤
      pv (splitVal (st.freeze P.TS) el P.NN XP) := by
  have hνS := nu2_mem_of_tauS P hS
  have hνL := nu2_mem_of_eLaw P hL
  have hν : ∀ q ∈ S ∪ L, 0 ≤ nu2 P q ∧ nu2 P q ≤ q := fun q hq => by
    rcases mem_union.1 hq with h | h
    · exact hνS q h
    · exact hνL q h
  refine (expect_hinge_tauSplit_le hPB hsub hSL hν (fun _ => N) hX P.NN acut60).trans ?_
  refine le_trans ?_ (splitVal_ge (st.freeze P.TS) el P.NN XP)
  rw [add_comm (pv (st.freeze P.TS).E * pv el.lost)]
  refine add_le_add (sum_le_sum fun e he => ?_) ?_
  · have he' := Nat.lt_succ_iff.1 (mem_range.1 he)
    have hW := hL.law N hN e he'
    have h0 : 0 ≤ (2 : ℝ) ^ e * lawE L (nu2 P) (fun _ => N) P.NN acut60 e :=
      mul_nonneg (by positivity) (lawE_nonneg hνL _ _ _ e)
    have hFB0 : 0 ≤ FB S (nu2 P) (fun _ => N) (X / 2 ^ e) := FB_nonneg hνS _ _
    have hy : pv (XP >>> e) ≤ X / 2 ^ e :=
      (pv_shiftRight_le XP e).trans (div_le_div_of_nonneg_right hXP (by positivity))
    have hFB : FB S (nu2 P) (fun _ => N) (X / 2 ^ e) ≤ pv (gsUp (st.freeze P.TS) (XP >>> e)) :=
      (FB_antitone hνS _ hy).trans (gsUp_sound P hS hN (XP >>> e))
    exact mul_le_mul hW hFB hFB0 (h0.trans hW)
  · rw [freeze_E]
    exact mul_le_mul (meanTau_le_pv P hS _) (hL.lost N hN) (lostE_nonneg hνL _ _ _)
      (pv_nonneg _)

/-- **(L2-B) Soundness of the τ-split cost** evaluated at `B ≤ p` (`B = p` in the per-prime
phase; `B` = the block start, `m ≤ B`, in the block phase), for a prime `p ≤ X` with `m ≤ 2B`,
the same δ at `B` and `p`, a valid weighted `τ_s` state for `S` and a valid e-law for `L`, where
`S` and `L` are disjoint and cover the primes below `p` (`L` may contain extra numbers: monotone
coupling). Exactly the statement of `Checker2Sound/Interfaces.lean`. -/
theorem splitCost_sound (P : Params2) {st : TauSState} {S : Finset ℕ} (hS : TauSValid P st S)
    {el : ELaw} {L : Finset ℕ} (hL : ELawValid P el L) (hSL : Disjoint S L) {p B : ℕ}
    (hp : p.Prime) (hB2 : 2 ≤ B) (hBp : B ≤ p) (hBp' : B = p ∨ P.m ≤ B) (hpX : p ≤ P.X)
    (hm : P.m ≤ 2 * B) (hsub : Nat.primesBelow p ⊆ S ∪ L) (hdn : deltaN2 P B = deltaN2 P p)
    (N : ℕ) :
    hingeLoss P.m (delta2 P) p (fun _ => N) ≤
      pv (splitCost P.m P.NN B (deltaN2 P B) (st.freeze P.TS) el) := by
  refine hingeLoss_le_of_forall_ge hp (fun q _ => delta2_nonneg P q)
    (fun q _ => delta2_le_half P q) 64 (fun N hN => ?_) N
  have hdnlt : deltaN2 P B < DDEN := deltaN2_lt_DDEN P B
  have hδp : delta2 P p = (deltaN2 P B : ℝ) / DDEN := by rw [delta2_of_le P hpX, hdn]
  have hDD : (0 : ℝ) < DDEN := by exact_mod_cast DDEN_pos
  have hdnR : (deltaN2 P B : ℝ) < DDEN := by exact_mod_cast hdnlt
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hB1 : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  have hBpR : (B : ℝ) ≤ p := by exact_mod_cast hBp
  -- the threshold
  set X : ℝ := (if p < P.m then 1 - 1 / (p : ℝ) else 0) + delta2 P p * ((p : ℝ) - 1) with hX
  have hc1 : 0 ≤ (if p < P.m then 1 - 1 / (p : ℝ) else 0) := by
    split_ifs
    · have : (1 : ℝ) / p ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      linarith
    · exact le_rfl
  have hX0 : 0 ≤ X := add_nonneg hc1 (mul_nonneg (delta2_nonneg P p) (by linarith))
  have hXP : pv (splitThreshold P.m B (deltaN2 P B)) ≤ X := by
    rw [hX, hδp]
    exact pv_splitThreshold_le (by omega) hBp hBp'
  -- step 2: the τ-split form of `hingeLoss`
  rw [hingeLoss_eq_tauSplit hp (by omega)]
  have hint : (fun v => max 0 (((smooth (Nat.primesBelow p) v).divisors.card : ℝ)
        - (if p < P.m then 1 - 1 / (p : ℝ) else 0) - delta2 P p * ((p : ℝ) - 1))) =
      fun v => max 0 (((smooth (Nat.primesBelow p) v).divisors.card : ℝ) - X) := by
    funext v
    rw [hX, sub_sub]
  rw [hint]
  -- steps 3–4: the numerator
  have hnum := expect_hinge_le_splitVal P hS hL hSL
    (fun q hq => Nat.prime_of_mem_primesBelow hq) hsub hN hX0 hXP
  -- step 5: the division
  have hV0 : 0 ≤ pv (splitVal (st.freeze P.TS) el P.NN (splitThreshold P.m B (deltaN2 P B))) :=
    pv_nonneg _
  have hden : ((p : ℝ) - 1) * (1 - delta2 P p) =
      ((p : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B) / DDEN := by
    rw [hδp]
    field_simp
  have hden0 : 0 < ((B : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B) :=
    mul_pos (by linarith) (by linarith)
  have hdenle : ((B : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B) ≤
      ((p : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  refine le_trans ?_ (splitCost_ge P.m P.NN B (deltaN2 P B) (st.freeze P.TS) el hB2 hdnlt)
  rw [hden, div_div_eq_mul_div]
  have hpd : 0 < ((p : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B) := mul_pos (by linarith) (by linarith)
  calc expect (Nat.primesBelow p) (tilt (delta2 P)) (fun _ => N)
        (fun v => max 0 (((smooth (Nat.primesBelow p) v).divisors.card : ℝ) - X)) * DDEN /
        (((p : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B))
      ≤ pv (splitVal (st.freeze P.TS) el P.NN (splitThreshold P.m B (deltaN2 P B))) * DDEN /
        (((p : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum hDD.le) hpd.le
    _ ≤ pv (splitVal (st.freeze P.TS) el P.NN (splitThreshold P.m B (deltaN2 P B))) * DDEN /
        (((B : ℝ) - 1) * ((DDEN : ℝ) - deltaN2 P B)) :=
        div_le_div_of_nonneg_left (mul_nonneg hV0 hDD.le) hden0 hdenle

end MinModulus.Checker2Sound.B
