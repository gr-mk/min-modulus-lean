import MinModulus.Tail2.CertT14501
import MinModulus.Tail2.Final

/-!
# Tail2.Main14501: least modulus `≤ 14500` (modulo the generic soundness of `run2`)

STATUS: complete, no `sorry` (L2-T). The only non-standard axiom is the `native_decide` axiom of
`Tail2.check2T14501_eq_true` (`CertT14501.lean`). The soundness of the frozen checker enters as the
hypothesis `E.Run2SoundStmt` (L2-E, `Checker2Sound/Run2Spec.lean`), or `E.Stage2Stmts` via
`E.run2_sound_of`. With `MinModulus.Checker2Sound.stage2Stmts : E.Stage2Stmts` (Interfaces.lean):
```lean
theorem not_covers_14501 … (hm : ∀ i, 14501 ≤ d i) : ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  Tail2.not_covers_14501_of_stage2 stage2Stmts d a hd hm
```
-/

namespace MinModulus.Tail2

open MinModulus.Checker2Impl MinModulus.Checker2Sound

/-- The side conditions of `run2_sound` for the target. -/
theorem sideOK_14501 : E.SideOK2 params14501 := by decide

/-- **Theorem (modulo `E.Run2SoundStmt`).** Congruences `a i (mod d i)` with distinct moduli
`d i ≥ 14501` do not cover `ℤ`: every covering system with distinct moduli has least modulus
`≤ 14500`. -/
theorem not_covers_14501_of (hsound : E.Run2SoundStmt) {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (a : ι → ℤ) (hd : Function.Injective d) (hm : ∀ i, 14501 ≤ d i) :
    ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  not_covers_of_check_2e9 hsound (P := params14501) (by decide) (by decide)
    sideOK_14501 check2T14501_eq_true d a hd hm

/-- The same from the bundle `E.Stage2Stmts` of the stage-2 statements. -/
theorem not_covers_14501_of_stage2 (hS2 : E.Stage2Stmts) {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (a : ι → ℤ) (hd : Function.Injective d) (hm : ∀ i, 14501 ≤ d i) :
    ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  not_covers_14501_of (run2SoundStmt_of hS2) d a hd hm

end MinModulus.Tail2
