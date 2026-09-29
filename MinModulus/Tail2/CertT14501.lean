import MinModulus.Tail2.Params14501
/-!
# `MinModulus.Tail2.CertT14501` — the checked Bool for `m = 14501`, `X = 2·10^9` (sharper tail)

Status: complete, no `sorry`. Core Lean only; **not** precompiled (default library `MinModulus`); it
imports the precompiled library `Checker2Impl`, whose shared library Lake loads, so `native_decide`
runs the frozen checker `run2` as native code.

This file contains exactly one `native_decide`. `check2T14501_eq_true` depends on `propext`,
`Classical.choice`, `Quot.sound` and the auxiliary axiom of Lean 4.34's `native_decide`
(`check2T14501_eq_true._native.native_decide.ax_…`).

## The target
`params14501` (`Params14501.lean`): `paramsFor 14501` with `X = 2·10^9`, the tail knots at `δ = 0.45`,
`TS = 2^22`. The final inequality uses the proved tail constant `5941/50000`
(`Tail2.tail2_2e9`): `etaA + etaB + etaC + ⌈T · 5941/(50000 · X)⌉ < 2^62`.
-/
namespace MinModulus.Tail2

/-- The checked Bool for the target `m = 14501`, `X = 2·10^9`, tail constant `5941/50000`. -/
def check2T14501 : Bool := checkWith2T 5941 50000 params14501

/-- The numeric certificate for `m = 14501`, evaluated by native code. -/
theorem check2T14501_eq_true : check2T14501 = true := by native_decide

end MinModulus.Tail2
