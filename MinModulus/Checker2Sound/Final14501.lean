import MinModulus.Checker2Sound.Interfaces
import MinModulus.Tail2.Main14501

/-!
# `Checker2Sound.Final14501`: least modulus `≤ 14500`, formally verified

STATUS: complete (fully proved). Wiring of L2-T's certificate by the coordinator, as `Final14505.lean`.
Not imported by anything else.

L2-T's `Tail2.not_covers_14501_of_stage2` (`Tail2/Main14501.lean`) proves non-covering for distinct
moduli `≥ 14501` from the bundle `E.Stage2Stmts` of the stage-2 statements. It uses:
* the frozen second checker `run2` at `Tail2.params14501`, i.e. `paramsFor 14501` with `X = 2·10^9`,
  the two tail knots at `δ = 0.45` and `TS = 2^22`, evaluated once by `native_decide` in
  `Tail2.check2T14501_eq_true` (about 10 minutes, 2.6 GB);
* L2-T's sharper elementary tail `T·5941/(50000·X)` for `X ≥ 2·10^9` (`Tail2.tail2_2e9`) and the chain
  `Tail2.not_covers_of_certT`;
* L2-E's generic soundness `E.run2_sound_of`.

Here the bundle is discharged by `stage2Stmts` (`Interfaces.lean`), which collects the owners'
theorems. Axioms of `not_covers_14501`: `propext`, `Classical.choice`, `Quot.sound` and
`MinModulus.Tail2.check2T14501_eq_true._native.native_decide.ax_1_1`.
-/

namespace MinModulus.Checker2Sound

/-- **Theorem.** Congruences `a i (mod d i)` with distinct moduli `d i ≥ 14501` do not cover `ℤ`:
every covering system with distinct moduli has least modulus `≤ 14500`. -/
theorem not_covers_14501 {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : Function.Injective d) (hm : ∀ i, 14501 ≤ d i) :
    ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  Tail2.not_covers_14501_of_stage2 stage2Stmts d a hd hm

end MinModulus.Checker2Sound
