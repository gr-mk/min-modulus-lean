import MinModulus.Checker2Sound.LoopPrimes
import MinModulus.Checker2Sound.LoopBlocks
import MinModulus.Checker2Sound.Run2Spec
import MinModulus.Checker2Impl.Certificate
import MinModulus.Main.Main

/-!
# `Checker2Sound.Assembly`: `run2_sound_of` and the certificate for `m = 14600` (L2-E)

STATUS: complete (fully proved). Owned by L2-E (namespace `MinModulus.Checker2Sound.E`).
Every theorem here takes the eight stage-2 statements as the hypothesis `hS2 : Stage2Stmts`
(`LoopStmts.lean`), so its `#print axioms` shows that everything else is proved:
`run2_sound_of`, `cert_of_run2_of`: `propext`, `Classical.choice`, `Quot.sound`;
`cert_14600_of`, `not_covers_14600_of`: these and `check2_eq_true`'s `native_decide` axiom.
`Interfaces.lean` instantiates them with the owners' theorems (`stage2Stmts`): `E.run2_sound`,
`E.cert_of_run2`, `cert_14600`, `not_covers_14600`.

* `run2_sound_of` (**generic**): for every `P` with the decidable side conditions `SideOK2 P`, a
  run with `(run2 P).ok = true` gives `Run2Facts P` (`Run2Spec.lean`): every field of
  `Main.Cert P.m P.X (delta2 P) c₀ T₀` except the final inequality, with
  `c₀ p = pv (costOf2 (run2 P) P p)`, `T₀ = pv (run2 P).T`, `Σ c₀ ≤ pv (etaA + etaB + etaC)`.
  Proof: the prime loop (`LoopPrimes.loop2_sound`), the block phase (`LoopBlocks.blockLoop2_spec`),
  `costOf2` (`costOf2_of_le/_of_gt`, `blockCost2_eq`), the δ facts (`LoopBasic`).
  No proof step unfolds `run2` at a concrete `P`.
* `cert_of_run2_of`: `checkWith2 P = true` + `SideOK2 P` ⟹ `Cert P.m P.X δ₀ c₀ T₀`
  (`checkWith2_spec`, `CheckerMath.cert_of_check`).
* `cert_14600_of`: `cert_of_run2_of … (paramsFor 14600) (by decide) check2_eq_true`; the only
  evaluation of the checker is `check2_eq_true` (`native_decide`).
-/

namespace MinModulus.Checker2Sound.E

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath MinModulus.Main

/-! ## `run2` as prime loop + block phase -/

/-- The frozen `τ_s` table used by the block phase of `run2 P`. -/
def tbFinal (P : Params2) : TauSTab :=
  match (loopFinal2 P).tb with
  | some tb => tb
  | none => (loopFinal2 P).tauS.freeze P.TS

/-- The block phase of `run2 P`. -/
def blockFinal2 (P : Params2) : BlkSt2 :=
  blockLoop2 P (sieve P.X) (tbFinal P) (deltaN2 P (P.PX + 1))
    ⟨0, (loopFinal2 P).T, (loopFinal2 P).el, #[]⟩ (P.PX + 1) (P.X + 1)

theorem run2_ok (P : Params2) :
    (run2 P).ok = ((loopFinal2 P).ok && schedOk P && decide (2 ≤ P.NN) && decide (P.m ≤ P.PX) &&
      decide (0 < deltaN2 P (P.PX + 1)) && decide (2 ^ 27 ≤ P.X) && decide (P.PX ≤ P.X)) := rfl
theorem run2_costs (P : Params2) : (run2 P).costs = (loopFinal2 P).costs := rfl
theorem run2_etaA (P : Params2) : (run2 P).etaA = (loopFinal2 P).etaA := rfl
theorem run2_etaB (P : Params2) : (run2 P).etaB = (loopFinal2 P).etaB := rfl
theorem run2_etaC (P : Params2) : (run2 P).etaC = (blockFinal2 P).etaC := rfl
theorem run2_T (P : Params2) : (run2 P).T = (blockFinal2 P).T := rfl
theorem run2_blocks (P : Params2) : (run2 P).blocks = (blockFinal2 P).blocks := rfl

theorem pv_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) : pv (∑ i ∈ s, f i) = ∑ i ∈ s, pv (f i) := by
  unfold pv
  push_cast
  rw [sum_div]

theorem primesLE_filter_gt_eq (PX X : ℕ) :
    (Nat.primesLE X).filter (PX < ·) = (Ico (PX + 1) (X + 1)).filter Nat.Prime := by
  ext q
  simp only [mem_filter, Nat.mem_primesLE, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h3⟩, by omega⟩

/-! ## The generic theorem -/

/-- **Soundness of a successful run of the second checker**, for any parameters satisfying the
decidable side conditions `SideOK2` (everything else is checked by `run2` itself). -/
theorem run2_sound_of (hS2 : Stage2Stmts) (P : Params2) (hP : SideOK2 P)
    (hok : (run2 P).ok = true) : Run2Facts P := by
  obtain ⟨hKH, hTS, hm5, hk0⟩ := hP
  rw [run2_ok] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hokL, hsched⟩, -⟩, hmPX⟩, -⟩, hX⟩, hPX⟩ := hok
  have hinv := loop2_sound hS2 hPX hm5 hKH hTS
  have hfin := doneSet_final P
  -- the standing hypotheses of the block phase
  have hBH : BlockHyp2 P (tbFinal P) (deltaN2 P (P.PX + 1)) (sSet P (primes2 P).size)
      (lSet P (primes2 P).size) :=
    { PX_le := hPX
      m_le := hmPX
      m5 := hm5
      dC_eq := fun p hp => deltaN2_const hsched hk0 hp (by omega)
      tst := ⟨(loopFinal2 P).tauS, hinv.tauS, by
        unfold tbFinal
        cases h : (loopFinal2 P).tb with
        | none => rfl
        | some t => exact (hinv.tb t h).1⟩
      S_le := fun q hq => (mem_doneSet_le P (mem_filter.1 hq).1 le_rfl).2
      L0_le := fun q hq => (mem_doneSet_le P (mem_filter.1 hq).1 le_rfl).2
      disj := disjoint_sSet_lSet P _
      cover := by rw [sSet_union_lSet, hfin] }
  obtain ⟨L, hL1, hL2, hL3, hL4, hL5, hL6⟩ := blockLoop2_spec hS2 hBH (P.X + 1)
    ⟨0, (loopFinal2 P).T, (loopFinal2 P).el, #[]⟩ (P.PX + 1) (by omega) (by omega)
    (by simpa [unm_self] using hinv.el)
  have hbl : (run2 P).blocks.toList = L := by
    rw [run2_blocks, blockFinal2, hL1]
    simp
  have hmax : max (P.PX + 1) (P.X + 1) = P.X + 1 := max_eq_right (by omega)
  have hch : Chain2 (P.PX + 1) (run2 P).blocks.toList (P.X + 1) := by
    rw [hbl, ← hmax]; exact hL2
  refine ⟨hX, fun p _ => delta2_nonneg P p, fun p _ => delta2_le_half P p,
    fun p _ hp => delta2_of_gt hp, ?_, ?_, ?_⟩
  · -- the per-prime losses
    intro p hp hpX N
    by_cases hle : p ≤ P.PX
    · rw [costOf2_of_le _ _ hle, run2_costs]
      exact hinv.cost hokL p (by rw [hfin]; exact Nat.mem_primesLE.2 ⟨hle, hp⟩) N
    · rw [costOf2_of_gt _ _ (not_le.1 hle)]
      obtain ⟨b, hb, h1, h2⟩ := Chain2.cover hch p (by omega) (by omega)
      rw [blockCost2_eq hch hb h1 h2]
      rw [hbl] at hb
      exact hL5 b hb p hp h1 h2 N
  · -- the sum of the costs
    rw [← sum_filter_add_sum_filter_not (Nat.primesLE P.X) (· ≤ P.PX), primesLE_filter_le hPX,
      pv_add]
    have e1 : ∑ p ∈ Nat.primesLE P.PX, pv (costOf2 (run2 P) P p) =
        pv ((run2 P).etaA + (run2 P).etaB) := by
      rw [run2_etaA, run2_etaB, hinv.eta, hfin, pv_sum]
      refine sum_congr rfl fun p hp => ?_
      rw [costOf2_of_le _ _ (Nat.mem_primesLE.1 hp).1, run2_costs]
    have e2 : (Nat.primesLE P.X).filter (fun p => ¬ p ≤ P.PX) =
        (Ico (P.PX + 1) (P.X + 1)).filter Nat.Prime := by
      rw [← primesLE_filter_gt_eq]
      exact filter_congr fun p _ => not_le
    rw [e1, e2]
    refine add_le_add le_rfl ?_
    have hsum := Chain2.sum_le (fun p => pv (costOf2 (run2 P) P p)) hch (by rw [hbl]; exact hL4)
      (fun b hb p hp h1 h2 => le_of_eq (by
        rw [costOf2_of_gt _ _ (by have := (Chain2.bounds hch).2 b hb; omega),
          blockCost2_eq hch hb h1 h2]))
    refine hsum.trans (le_of_eq ?_)
    rw [list_sum_pv, run2_etaC, hbl]
    have h3 : (blockFinal2 P).etaC = 0 + (L.map fun b => b.count * b.val).sum := hL3
    rw [h3, zero_add]
  · -- the product of the tail factors
    rw [run2_T]
    have hT0 : ∏ q ∈ Nat.primesBelow (P.PX + 1), tailFactor (delta2 P) q ≤
        pv (⟨0, (loopFinal2 P).T, (loopFinal2 P).el, #[]⟩ : BlkSt2).T := by
      have h := hinv.T
      rw [hfin] at h
      exact h
    have h := hL6 hT0
    rw [hmax] at h
    exact h

theorem run2_sound_stmt_of (hS2 : Stage2Stmts) : Run2SoundStmt :=
  fun P hP hok => run2_sound_of hS2 P hP hok

/-- **The certificate from a successful check**, for any parameters satisfying `SideOK2`. -/
theorem cert_of_run2_of (hS2 : Stage2Stmts) (P : Params2) (hP : SideOK2 P)
    (hchk : checkWith2 P = true) :
    Cert P.m P.X (delta2 P) (fun p => pv (costOf2 (run2 P) P p)) (pv (run2 P).T) := by
  obtain ⟨hok, htot⟩ := checkWith2_spec hchk
  have hF := run2_sound_of hS2 P hP hok
  have hfun : (fun p => pv (costOf2 (run2 P) P p)) =
      (fun p => ((costOf2 (run2 P) P p : ℕ) : ℝ) / (ONE : ℕ)) :=
    funext fun p => pv_eq_div_ONE _
  rw [hfun, pv_eq_div_ONE]
  refine cert_of_check hF.two_pow_le (deltaCert2 P) (fun p _ => two_mul_deltaCert2_le P p)
    (fun p _ hp => deltaCert2_of_gt hp) (costOf2 (run2 P) P) ONE_pos
    (e := (run2 P).etaA + (run2 P).etaB + (run2 P).etaC) ?_ ?_ ?_ ?_
  · intro p hp hpX N
    rw [← pv_eq_div_ONE]
    exact hF.loss_le p hp hpX N
  · simp only [← pv_eq_div_ONE]
    exact hF.sum_le
  · rw [← pv_eq_div_ONE]
    exact hF.prod_le
  · simpa only [Result2.total, tailUp2, cdiv] using htot

/-! ## The target `m = 14600` -/

theorem sideOK2_14600 : SideOK2 (paramsFor 14600) := by decide

/-- **The numeric certificate** for `m = 14600`, `X = 2·10^8`, given the stage-2 statements. -/
theorem cert_14600_of (hS2 : Stage2Stmts) :
    ∃ (δ c : ℕ → ℝ) (T : ℝ), Cert 14600 (2 * 10 ^ 8) δ c T :=
  ⟨_, _, _, cert_of_run2_of hS2 (paramsFor 14600) sideOK2_14600 check2_eq_true⟩

/-- The final theorem, given the stage-2 statements (for the audit). -/
theorem not_covers_14600_of (hS2 : Stage2Stmts) {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (a : ι → ℤ) (hd : Function.Injective d) (hm : ∀ i, 14600 ≤ d i) :
    ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) := by
  obtain ⟨δ, c, T, hc⟩ := cert_14600_of hS2
  exact Main.not_covers_of_cert hc (by norm_num) d a hd hm

end MinModulus.Checker2Sound.E
