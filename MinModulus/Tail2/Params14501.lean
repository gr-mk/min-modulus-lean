import MinModulus.Tail2.CheckT
/-!
# `MinModulus.Tail2.Params14501` — the parameters of the `m = 14501` target

Status: definitions only (core Lean, not precompiled). All fields are data of the frozen checker
(`Checker2Impl.Params2`); no checker code is changed. Relative to `paramsFor 14501`:
* `X = 2·10^9` (the explicit range; the tail constant is then `5941/50000`, `Tail2.tail2_2e9`);
* `kds = knotDs45` (the two tail knots at `δ = 0.45`, see `CheckT.lean`);
* `TS = 2^22` (the `τ_s` law on `[0, 2^22]` instead of `2^20`; prototype: `η` lower by ≈ 8.5·10^-6).

(`epsShift = 40` would lower `η` by another ≈ 3·10^-6 in the prototype, but the Lean DFS then runs into
big-number arithmetic and takes > 13 min for the S/B/H range alone; the frozen `epsShift = 33` is kept.)
`run2_sound` (L2-E) is generic in all these fields; `SideOK2` holds (`1 ≤ KH`, `1 ≤ TS`, `5 ≤ m`,
`kps[0] ≤ PX`).
-/
namespace MinModulus.Tail2

open MinModulus.Checker2Impl

/-- The parameters of the `m = 14501` target. -/
def params14501 : Params2 :=
  { paramsFor 14501 with X := 2000000000, kds := knotDs45, TS := 4194304 }

end MinModulus.Tail2
