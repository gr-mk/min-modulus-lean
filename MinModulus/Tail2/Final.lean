import MinModulus.Tail2.Chain
import MinModulus.Tail2.CheckT
import MinModulus.Checker2Sound.Assembly

/-!
# Tail2.Final: non-covering from a `checkWith2T` run and the generic soundness of `run2`

STATUS: complete, no `sorry` (L2-T). The soundness of the frozen checker `run2` enters only through
L2-E's generic statement: either `E.Run2SoundStmt` (`Checker2Sound/Run2Spec.lean`) or the bundle
`E.Stage2Stmts` via `E.run2_sound_of` (`Checker2Sound/Assembly.lean`); both are hypotheses here.

## Main results
* `certT_of_check_1e9` / `certT_of_check_2e8` / `certT_of_check_2e9`: from `SideOK2 P`, `checkWith2T Cn Cd P = true` and
  the soundness statement, a `CertT P.m P.X (delta2 P) c₀ T₀ (Cn/Cd/X)` with the proved tail constant.
* `not_covers_of_check_1e9` / `not_covers_of_check_2e8` / `not_covers_of_check_2e9`: hence no covering with distinct moduli `≥ m`.
-/

namespace MinModulus.Tail2

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath MinModulus.Main
  MinModulus.Checker2Sound

/-- The final inequality in real form: `Σ c₀ + T₀ · Cn/(Cd X) < 1` from the checked Nat inequality. -/
theorem total_lt_of_checkT {Cn Cd : ℕ} {P : Params2} (hCd : 0 < Cd) (hX : 0 < P.X)
    (F : E.Run2Facts P)
    (h : (run2 P).etaA + (run2 P).etaB + (run2 P).etaC + tailUpT Cn Cd P (run2 P).T < ONE) :
    ∑ p ∈ Nat.primesLE P.X, pv (costOf2 (run2 P) P p) +
      pv (run2 P).T * ((Cn : ℝ) / Cd / (P.X : ℝ)) < 1 := by
  have hsum := F.sum_le
  set e := (run2 P).etaA + (run2 P).etaB + (run2 P).etaC
  set t := tailUpT Cn Cd P (run2 P).T with ht
  -- `pv T · Cn/(Cd X) ≤ pv t`
  have htail : pv (run2 P).T * ((Cn : ℝ) / Cd / (P.X : ℝ)) ≤ pv t := by
    have hpos : 0 < Cd * P.X := Nat.mul_pos hCd hX
    have hc := cdiv_ge (a := (run2 P).T * Cn) hpos
    rw [ht, tailUpT, E.pv_eq_div_ONE, E.pv_eq_div_ONE]
    have hONE : (0 : ℝ) < (ONE : ℕ) := by exact_mod_cast (show 0 < ONE by decide)
    have e1 : ((run2 P).T : ℝ) / (ONE : ℕ) * ((Cn : ℝ) / Cd / (P.X : ℝ)) =
        (((run2 P).T * Cn : ℕ) : ℝ) / ((Cd * P.X : ℕ) : ℝ) / (ONE : ℕ) := by
      push_cast
      field_simp
    rw [e1]
    exact div_le_div_of_nonneg_right hc hONE.le
  have hlt : pv (e + t) < 1 := by
    rw [← E.pv_ONE]
    rw [E.pv_eq_div_ONE, E.pv_eq_div_ONE]
    have hONE : (0 : ℝ) < (ONE : ℕ) := by exact_mod_cast (show 0 < ONE by decide)
    apply div_lt_div_of_pos_right _ hONE
    exact_mod_cast h
  rw [E.pv_add] at hlt
  linarith

/-- A successful `checkWith2T 12473 100000 P` run with `X ≥ 10^9` is a `CertT` (given the generic
soundness of `run2`). -/
theorem certT_of_check_1e9 (hsound : E.Run2SoundStmt) {P : Params2} (hX : 10 ^ 9 ≤ P.X)
    (hside : E.SideOK2 P) (hchk : checkWith2T 12473 100000 P = true) :
    CertT P.m P.X (delta2 P) (fun p => pv (costOf2 (run2 P) P p)) (pv (run2 P).T)
      (12473 / 100000 / (P.X : ℝ)) := by
  obtain ⟨hok, htot⟩ := checkWith2T_spec hchk
  have F := hsound P hside hok
  have ht := total_lt_of_checkT (by norm_num) (by omega) F htot
  push_cast at ht
  exact CertT.of_facts_1e9 hX F.delta_nonneg F.delta_le_half F.delta_tail F.loss_le F.prod_le ht

/-- A successful `checkWith2T 7051 50000 P` run with `X ≥ 2·10^8` is a `CertT` (given the generic
soundness of `run2`). -/
theorem certT_of_check_2e8 (hsound : E.Run2SoundStmt) {P : Params2} (hX : 2 * 10 ^ 8 ≤ P.X)
    (hside : E.SideOK2 P) (hchk : checkWith2T 7051 50000 P = true) :
    CertT P.m P.X (delta2 P) (fun p => pv (costOf2 (run2 P) P p)) (pv (run2 P).T)
      (7051 / 50000 / (P.X : ℝ)) := by
  obtain ⟨hok, htot⟩ := checkWith2T_spec hchk
  have F := hsound P hside hok
  have ht := total_lt_of_checkT (by norm_num) (by omega) F htot
  push_cast at ht
  exact CertT.of_facts_2e8 hX F.delta_nonneg F.delta_le_half F.delta_tail F.loss_le F.prod_le ht

/-- **Non-covering from a checked run** (`X ≥ 10^9`, tail constant `12473/100000`). -/
theorem not_covers_of_check_1e9 (hsound : E.Run2SoundStmt) {P : Params2} (hX : 10 ^ 9 ≤ P.X)
    (hm : 2 ≤ P.m) (hside : E.SideOK2 P) (hchk : checkWith2T 12473 100000 P = true)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ) (hd : Function.Injective d)
    (hdm : ∀ i, P.m ≤ d i) : ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  not_covers_of_certT (certT_of_check_1e9 hsound hX hside hchk) hm d a hd hdm

/-- **Non-covering from a checked run** (`X ≥ 2·10^8`, tail constant `7051/50000`). -/
theorem not_covers_of_check_2e8 (hsound : E.Run2SoundStmt) {P : Params2} (hX : 2 * 10 ^ 8 ≤ P.X)
    (hm : 2 ≤ P.m) (hside : E.SideOK2 P) (hchk : checkWith2T 7051 50000 P = true)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ) (hd : Function.Injective d)
    (hdm : ∀ i, P.m ≤ d i) : ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  not_covers_of_certT (certT_of_check_2e8 hsound hX hside hchk) hm d a hd hdm

/-- A successful `checkWith2T 5941 50000 P` run with `X ≥ 2·10^9` is a `CertT` (given the generic
soundness of `run2`). -/
theorem certT_of_check_2e9 (hsound : E.Run2SoundStmt) {P : Params2} (hX : 2 * 10 ^ 9 ≤ P.X)
    (hside : E.SideOK2 P) (hchk : checkWith2T 5941 50000 P = true) :
    CertT P.m P.X (delta2 P) (fun p => pv (costOf2 (run2 P) P p)) (pv (run2 P).T)
      (5941 / 50000 / (P.X : ℝ)) := by
  obtain ⟨hok, htot⟩ := checkWith2T_spec hchk
  have F := hsound P hside hok
  have ht := total_lt_of_checkT (by norm_num) (by omega) F htot
  push_cast at ht
  exact CertT.of_facts_2e9 hX F.delta_nonneg F.delta_le_half F.delta_tail F.loss_le F.prod_le ht

/-- **Non-covering from a checked run** (`X ≥ 2·10^9`, tail constant `5941/50000`). -/
theorem not_covers_of_check_2e9 (hsound : E.Run2SoundStmt) {P : Params2} (hX : 2 * 10 ^ 9 ≤ P.X)
    (hm : 2 ≤ P.m) (hside : E.SideOK2 P) (hchk : checkWith2T 5941 50000 P = true)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ) (hd : Function.Injective d)
    (hdm : ∀ i, P.m ≤ d i) : ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  not_covers_of_certT (certT_of_check_2e9 hsound hX hside hchk) hm d a hd hdm

/-- `E.Stage2Stmts` (the bundle of the stage-2 statements) gives `E.Run2SoundStmt`. -/
theorem run2SoundStmt_of (hS2 : E.Stage2Stmts) : E.Run2SoundStmt :=
  fun P hP hok => E.run2_sound_of hS2 P hP hok

end MinModulus.Tail2
