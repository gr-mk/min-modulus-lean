import MinModulus.Checker2Impl.Checker
/-!
# `MinModulus.Tail2.CheckT` — the checked Bool of the second checker with the sharper tail

Status: definitions only (core Lean, no Mathlib, not precompiled). The frozen checker `run2`
(`Checker2Impl`, precompiled) is reused unchanged; only the final inequality differs from
`checkWith2`: the tail term is `⌈T · Cn / (Cd · X)⌉` (P-value) with the proved constant
`Cn/Cd` of `Tail2` (`7051/50000` for `X ≥ 2·10^8`, `12473/100000` for `X ≥ 10^9`) instead of
`⌈T · 100 / (189 X)⌉`.

The certificate theorems (one `native_decide` per target) are in `Tail2/CertT.lean` (`m = 14505`,
`X = 10^9`) and `Tail2/CertT14501.lean` (`m = 14501`, `X = 2·10^9`, parameters in `Params14501.lean`).
-/
namespace MinModulus.Tail2

open MinModulus.CheckerImpl MinModulus.Checker2Impl

/-- Upper P-value of the tail term `T · Cn/(Cd · X)` (`T` a P-value). -/
def tailUpT (Cn Cd : Nat) (P : Params2) (T : Nat) : Nat := cdiv (T * Cn) (Cd * P.X)

/-- The checked Bool with the tail constant `Cn/Cd`: the run succeeded and
`etaA + etaB + etaC + ⌈T · Cn/(Cd · X)⌉ < 2^62`. -/
def checkWith2T (Cn Cd : Nat) (P : Params2) : Bool :=
  let r := run2 P
  r.ok && decide (r.etaA + r.etaB + r.etaC + tailUpT Cn Cd P r.T < ONE)

/-- What the checked Bool means. -/
theorem checkWith2T_spec {Cn Cd : Nat} {P : Params2} (h : checkWith2T Cn Cd P = true) :
    (run2 P).ok = true ∧
      (run2 P).etaA + (run2 P).etaB + (run2 P).etaC + tailUpT Cn Cd P (run2 P).T < ONE := by
  unfold checkWith2T at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- The parameters of the target: `paramsFor m` (frozen schedule and settings) with the explicit
range `X`. -/
def paramsT (m X : Nat) : Params2 := { paramsFor m with X := X }

/-- The frozen knot values `knotDs` with the last two knots (`p = 50000` and `p = 200000`, hence
`δ` for every `p ≥ 50000`) raised from `0.42` to `0.45` (the clamp `DNMAX2`). With the sharper tail
the tail term is small, and the larger tail `δ` lowers `η` more than it raises `T · C/X`
(prototype, `m = 14510`, `X = 10^9`: slack `1.09·10^-5` at `0.42`, `9.60·10^-5` at `0.45`). This is
close to the original `m = 14501` schedule (`0.4492`, `0.46`). -/
def knotDs45 : Array Nat := (knotDs.pop.pop).push 450000 |>.push 450000

/-- The parameters with the raised tail knots (`knotDs45`) and the explicit range `X`. -/
def params45 (m X : Nat) : Params2 := { paramsFor m with X := X, kds := knotDs45 }

end MinModulus.Tail2
