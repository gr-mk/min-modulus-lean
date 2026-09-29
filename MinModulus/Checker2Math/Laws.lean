import MinModulus.CheckerMath.TauLaw

/-!
# `Checker2Math.Laws`: the new laws of the second checker (definitions)

STATUS: definitions only (lean2 stage 1), no `sorry`. The lemmas about them are stage-2 work
(`Checker2Math/SBHLaw*.lean`: agent L2-A; `Checker2Math/SplitLaw*.lean`: agent L2-B); see
`SCRATCH/agents/lean2/LEAN2_DESIGN.md`.

All laws are under Smooth's capped tilted product law (`Smooth.expect Ps ν γ`), exactly like
`CheckerMath.TauLaw` (`tauN`, `Kept`, `lawKept`, `lostMass`, `lawTau`), which the second checker
reuses unchanged for `T_H` (`lawTau`, the exact law: the lower-tail tables need no truncation) and for
`τ_s` (`lawKept`, `lostMass`, table `[0, TS]`, exponent cut `acut60`).

* `bstat R a w = Σ_{q ∈ R, w q ≥ 1} a q`: the statistic `b` of the S/B/H bound (`a q` = the profile
  `a_q(s_S)` on `B`, `0` on `H`).
* `lawJoint R a ν γ k j = P(τ_R = k ∧ b = j)`: the joint law of the S/B/H lower-tail tables (exact).
* `estat L w = Σ_{q ∈ L} w q` (`τ_L ≤ 2^{estat}`), `KeptE`, `lawE = P(e = ·, kept)`,
  `lostE = E[2^e; ¬kept]`: the e-law of the τ-split.
-/

namespace MinModulus.Checker2Math

open Finset MinModulus.Smooth MinModulus.CheckerMath

/-- `b(w) = Σ_{q ∈ R, w q ≥ 1} a q`. -/
def bstat (R : Finset ℕ) (a : ℕ → ℕ) (w : ℕ → ℕ) : ℕ := ∑ q ∈ R, if 1 ≤ w q then a q else 0

/-- The joint law `P(τ_R = k ∧ b = j)` (exact; capped tilted law). -/
noncomputable def lawJoint (R : Finset ℕ) (a : ℕ → ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (k j : ℕ) : ℝ :=
  expect R ν γ (fun w => if tauN R w = k ∧ bstat R a w = j then 1 else 0)

/-- `e(w) = Σ_{q ∈ L} w q`. -/
def estat (L : Finset ℕ) (w : ℕ → ℕ) : ℕ := ∑ q ∈ L, w q

/-- The e-DP keeps `w` iff `e(w) ≤ NN` and every exponent is `≤ acut q`. -/
def KeptE (L : Finset ℕ) (NN : ℕ) (acut : ℕ → ℕ) (w : ℕ → ℕ) : Prop :=
  estat L w ≤ NN ∧ ∀ q ∈ L, w q ≤ acut q

instance (L : Finset ℕ) (NN : ℕ) (acut : ℕ → ℕ) : DecidablePred (KeptE L NN acut) :=
  fun w => inferInstanceAs (Decidable (estat L w ≤ NN ∧ ∀ q ∈ L, w q ≤ acut q))

/-- `P(e = e₀ ∧ kept)`. -/
noncomputable def lawE (L : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) (e₀ : ℕ) :
    ℝ :=
  expect L ν γ (fun w => if estat L w = e₀ ∧ KeptE L NN acut w then 1 else 0)

/-- `E[2^e ; ¬ kept]`. -/
noncomputable def lostE (L : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) : ℝ :=
  expect L ν γ (fun w => if KeptE L NN acut w then 0 else (2 : ℝ) ^ estat L w)

end MinModulus.Checker2Math
