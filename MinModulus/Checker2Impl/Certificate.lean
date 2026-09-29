import MinModulus.Checker2Impl.Checker
/-
# `MinModulus.Checker2Impl.Certificate` — the checked Bool for `m = 14600`, `X = 2·10^8`

Status: complete, no `sorry`. Core Lean only. This module is **not** precompiled (Lake library
`Checker2Cert`); it imports the precompiled library `Checker2Impl`, so `native_decide` below runs
the checker as native code (about 70 s, 0.3 GB).

`check2_eq_true` depends on `propext`, `Classical.choice`, `Quot.sound` and the auxiliary axiom
that Lean 4.34's `native_decide` introduces for the evaluated Bool
(`check2_eq_true._native.native_decide.ax_…`), i.e. it trusts the compiled evaluation of `check2`.

## Certificate data (for the soundness proof; `P := paramsFor 14600`, `r := run2 P`)
* `δ₀ p := (deltaCert2 P p).1 / (deltaCert2 P p).2` — `deltaN2 P p / 10^9` for `p ≤ X`, `1/2` beyond;
* `c₀ p := costOf2 r P p / 2^62`;
* `T₀ := r.T / 2^62`.
`checkWith2_spec` turns `check2 = true` into `r.ok = true ∧ r.etaA + r.etaB + r.etaC +
cdiv (r.T·100) (189 X) < 2^62`, the hypothesis shape of `CheckerMath.cert_of_check`.

## The run (native, `lake exe checker2 14600`)
`η_up = 0.998668891654` (first moment `p < 17`: `0.036832937126`; `17 ≤ p ≤ 2·10^5`:
`0.960448727804`; blocks `2·10^5 < p ≤ 2·10^8`: `0.001387226724`), `T_up = 360512.98941187`,
tail `0.000953738068`, total `0.999622629721 < 1` (slack `3.77·10^-4`).
-/
namespace MinModulus.Checker2Impl

/-- The checked Bool for the target `m = 14600` (`X = 2·10^8`, `paramsFor`). -/
def check2 : Bool := checkWith2 (paramsFor 14600)

/-- The numeric certificate of the second checker, evaluated by native code. -/
theorem check2_eq_true : check2 = true := by native_decide

end MinModulus.Checker2Impl
