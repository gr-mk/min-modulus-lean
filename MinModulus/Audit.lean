import MinModulus.Checker2Sound.Final14501

/-!
# Axiom audit

`lake build MinModulus.Audit` prints the axioms of the main theorem (least modulus ≤ 14,500) and of the first
formalization it builds on (least modulus ≤ 15,999). Expected output:

* `MinModulus.Checker2Sound.not_covers_14501`: `propext`, `Classical.choice`, `Quot.sound`,
  `MinModulus.Tail2.check2T14501_eq_true._native.native_decide.ax_1_1`;
* `MinModulus.not_covers`: `propext`, `Classical.choice`, `Quot.sound`,
  `MinModulus.CheckerImpl.check_eq_true._native.native_decide.ax_1_1`.
-/

#check @MinModulus.Checker2Sound.not_covers_14501
#print axioms MinModulus.Checker2Sound.not_covers_14501
#print axioms MinModulus.not_covers
