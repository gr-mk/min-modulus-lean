import MinModulus.CheckerSound.Loop
import MinModulus.CheckerImpl.Certificate

/-!
# `CheckerSound.Assembly`: the numeric certificate `cert_16000`

STATUS: complete, no `sorry`. `cert_16000` (hence `MinModulus.not_covers`) depends on `propext`,
`Classical.choice`, `Quot.sound` and `CheckerImpl.check_eq_true._native.native_decide.ax_1_1`
only (`CheckerSound/Audit.lean`).

Owned by CS-D. Assembles `Main.Cert 16000 (2·10^8) δ₀ c₀ T₀` from
* the checked Bool `CheckerImpl.check_eq_true` (`native_decide`) and `checkWith_spec`;
* the prime loop (`Loop.lean`: `loop_sound`, CS-D);
* the block phase (`blockPhase_cost_sound`, `blockPhase_sum_le`, `blockPhase_T_le`, CS-A);
* `CheckerMath.cert_of_check` (Glue).

The data: `P = fullParams`, `r = run P`,
* `δ₀ = delta0 P = deltaPairR (deltaCert P)` (`deltaN P p / 10^9` for `p ≤ X`, `1/2` beyond);
* `c₀ p = costOf r P p / 2^62`;
* `T₀ = r.T / 2^62`.

Everything is proved for a **general** `P` (`cert_of_run`), so that no proof step can unfold
`run fullParams`; the only evaluation of the checker is `check_eq_true` (`native_decide`).
-/

namespace MinModulus.CheckerSound.D

open Finset MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Main MinModulus.CheckerSound

/-! ## The certificate for a general parameter set -/

section General

variable (hCC : ComparisonCostSound) {P : Params} {dC : ℕ} (hPX : P.PX ≤ P.PMAX)
  (hK : 1 ≤ P.KMAX) (hB : BlockHyp P dC)
include hCC hPX hK hB

/-- `Σ_{p ≤ X prime} c₀ p ≤ (etaA + etaB + etaC)/2^62`. -/
theorem sum_costs_le :
    ∑ p ∈ Nat.primesLE P.PMAX, ((costOf (run P) P p : ℕ) : ℝ) / (ONE : ℕ) ≤
      (((run P).etaA + (run P).etaB + (run P).etaC : ℕ) : ℝ) / (ONE : ℕ) := by
  obtain ⟨heta, -, -⟩ := loop_sound hCC P hPX hK
  have hsum := blockPhase_sum_le P hB (loopFinal P).ET2 (loopFinal P).ET25 (loopFinal P).ET3
  simp only [← pv_eq_div_ONE]
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE P.PMAX) (· ≤ P.PX),
    primesLE_filter_le hPX]
  have e1 : ∑ p ∈ Nat.primesLE P.PX, pv (costOf (run P) P p) =
      pv ((run P).etaA + (run P).etaB) := by
    rw [run_etaA, run_etaB, heta]
    unfold pv
    push_cast
    rw [← sum_div]
    refine congrArg (· / (2 : ℝ) ^ 62) (sum_congr rfl fun p hp => ?_)
    rw [costOf_of_le _ _ (Nat.mem_primesLE.1 hp).1, run_costs]
  have e2 : ∑ p ∈ (Nat.primesLE P.PMAX).filter (fun p => ¬ p ≤ P.PX), pv (costOf (run P) P p) =
      ∑ p ∈ (Nat.primesLE P.PMAX).filter (P.PX < ·),
        pv (blockCost (blockPhase P (loopFinal P).ET2 (loopFinal P).ET25
          (loopFinal P).ET3).blocks p) := by
    rw [filter_congr fun p _ => not_le]
    refine sum_congr rfl fun p hp => ?_
    rw [costOf_of_gt _ _ (mem_filter.1 hp).2, run_blocks]
  rw [e1, e2, pv_add ((run P).etaA + (run P).etaB), run_etaC]
  exact add_le_add le_rfl hsum

/-- **The certificate from a successful run**, for any parameters satisfying the standing
hypotheses (`X ≥ 2^27`, `PX ≤ X`, `KMAX ≥ 1`, constant positive `δ` on `(PX, X]`). -/
theorem cert_of_run (hX : 2 ^ 27 ≤ P.PMAX) (hchk : checkWith P = true) :
    Cert P.m P.PMAX (delta0 P) (fun p => ((costOf (run P) P p : ℕ) : ℝ) / (ONE : ℕ))
      ((((run P).T : ℕ) : ℝ) / (ONE : ℕ)) := by
  obtain ⟨hok, htot⟩ := checkWith_spec hchk
  rw [run_ok] at hok
  obtain ⟨-, hET, hcost⟩ := loop_sound hCC P hPX hK
  refine cert_of_check hX (deltaCert P) (fun p _ => two_mul_deltaCert_le P p)
    (fun p _ hp => deltaCert_of_gt hp) (costOf (run P) P) (K := ONE) (by decide) ?_
    (sum_costs_le hCC hPX hK hB) ?_ ?_
  · -- the per-prime losses
    intro p hp hpX N
    rw [← pv_eq_div_ONE]
    show hingeLoss P.m (delta0 P) p (fun _ => N) ≤ pv (costOf (run P) P p)
    by_cases hle : p ≤ P.PX
    · rw [costOf_of_le _ _ hle, run_costs]
      exact hcost hok p hp hle N
    · rw [costOf_of_gt _ _ (not_le.1 hle), run_blocks]
      exact blockPhase_cost_sound P hB hET hp (not_le.1 hle) hpX N
  · -- the product of the tail factors
    rw [← pv_eq_div_ONE, run_T]
    exact blockPhase_T_le P hB hET
  · -- the checked inequality
    simpa only [Result.total, tailUp, cdiv] using htot

end General

/-! ## `fullParams` -/

theorem full_PX_le : fullParams.PX ≤ fullParams.PMAX := by decide

theorem full_KMAX : 1 ≤ fullParams.KMAX := by decide

theorem full_two_pow_le : 2 ^ 27 ≤ fullParams.PMAX := by decide

/-- `δ = 0.4092` on the whole block range `(PX, X]` (the last knot is `50000 < PX`). -/
theorem full_deltaN_of_gt {p : ℕ} (h : fullParams.PX < p) : deltaN fullParams p = 409200000 := by
  have hPX : fullParams.PX = 200000 := rfl
  rw [hPX] at h
  have h1 : ¬ p < 50 := by omega
  have h2 : ¬ p ≤ 50 := by omega
  have h3 : 50000 ≤ p := by omega
  simp [deltaN, fullParams, knotDelta, h1, h2, h3, dnOfTenThousandths, DNMAX]

theorem full_blockHyp : BlockHyp fullParams 409200000 where
  one_le_PX := by decide
  PX_le := full_PX_le
  dC_pos := by decide
  const := fun _ h _ => full_deltaN_of_gt h

/-- The numeric certificate for `m = 16000`, `X = 2·10^8`, given the soundness of
`comparisonCost` (CS-C). -/
theorem cert_16000_of (hCC : ComparisonCostSound) :
    ∃ (δ c : ℕ → ℝ) (T : ℝ), Cert 16000 (2 * 10 ^ 8) δ c T :=
  ⟨_, _, _, cert_of_run hCC full_PX_le full_KMAX full_blockHyp full_two_pow_le check_eq_true⟩

/-- **The numeric certificate** for `m = 16000`, `X = 2·10^8`. -/
theorem cert_16000 : ∃ (δ c : ℕ → ℝ) (T : ℝ), Cert 16000 (2 * 10 ^ 8) δ c T :=
  cert_16000_of comparisonCostSound

end MinModulus.CheckerSound.D
