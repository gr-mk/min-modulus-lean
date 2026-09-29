import MinModulus.Main.Certificate
import MinModulus.Smooth.Bounds

/-!
# CheckerMath, shared bridge: `hingeLoss` with upper bounds on the tilts

STATUS: complete, no `sorry`. Owned by the CheckerMath (first moment / moments / glue) agent.

The certificate `Main.Cert` uses the **exact** tilts `tilt δ q = 1/(1 - δ q)`. A checker works
with rational (or dyadic) upper bounds `ν q ≥ tilt δ q`. Since the hinge integrand
`v ↦ max 0 (U_p(s(v)) - δ p)` is monotone, the expectation is monotone in the tilts
(`Smooth.expect_mono_tilt`), so every bound proved with the tilts `ν` is a bound for `hingeLoss`.

* `hingeLoss_eq_div` : `hingeLoss m δ p γ = E_{tilt δ,γ}[max 0 (U_p(s) - δ p)] / (1 - δ p)`;
* `hingeLoss_le_of_tilt_le` : the same with any tilts `ν`, `tilt δ q ≤ ν q ≤ q` below `p`, as an
  upper bound;
* `tilt_le_iff` : the rational side condition `tilt δ q ≤ ν ↔ 1 ≤ ν (1 - δ q)`;
* `tilt_eq_one_of_eq_zero` : `δ q = 0 → tilt δ q = 1`;
* `tilt_mem_self`, `delta_le_one_of_le_half` : the tilt/δ hypotheses for `ν := tilt δ` (the landed
  checker uses exact tilts `ν = 10^9/(10^9 - dn)`).

This file is the shared entry point for every per-prime bound of the certificate (first moment,
θ-moments, and the comparison-bound layer): prove the bound for the checker's tilts `ν`, then
conclude with `hingeLoss_le_of_tilt_le`.
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth MinModulus.Main

theorem tilt_nonneg {δ : ℕ → ℝ} {q : ℕ} (h : δ q ≤ 1) : 0 ≤ tilt δ q := by
  unfold tilt
  exact div_nonneg zero_le_one (by linarith)

theorem tilt_pos {δ : ℕ → ℝ} {q : ℕ} (h : δ q < 1) : 0 < tilt δ q := by
  unfold tilt
  exact div_pos zero_lt_one (by linarith)

/-- Rational side condition for a tilt upper bound: `tilt δ q ≤ ν ↔ 1 ≤ ν · (1 - δ q)`. -/
theorem tilt_le_iff {δ : ℕ → ℝ} {q : ℕ} (h : δ q < 1) {ν : ℝ} :
    tilt δ q ≤ ν ↔ 1 ≤ ν * (1 - δ q) := by
  unfold tilt
  rw [div_le_iff₀ (by linarith)]

theorem tilt_eq_one_of_eq_zero {δ : ℕ → ℝ} {q : ℕ} (h : δ q = 0) : tilt δ q = 1 := by
  simp [tilt, h]

/-- `hingeLoss` with the constant factor `1/(1 - δ p)` pulled out of the expectation. -/
theorem hingeLoss_eq_div (m : ℕ) (δ : ℕ → ℝ) (p : ℕ) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ = expect (Nat.primesBelow p) (tilt δ) γ
      (fun v => max 0 (Up p m (smooth (Nat.primesBelow p) v) - δ p)) / (1 - δ p) := by
  unfold hingeLoss
  simp_rw [div_eq_mul_inv]
  exact expect_mul_const _ _

/-- **Tilt bridge.** If `tilt δ q ≤ ν q ≤ q` for every prime `q < p`, then `hingeLoss` is at most
the same hinge expectation under the tilts `ν`. -/
theorem hingeLoss_le_of_tilt_le {m p : ℕ} {δ : ℕ → ℝ} (hp : 1 < p) (hδp : δ p < 1)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ expect (Nat.primesBelow p) ν γ
      (fun v => max 0 (Up p m (smooth (Nat.primesBelow p) v) - δ p)) / (1 - δ p) := by
  rw [hingeLoss_eq_div]
  refine div_le_div_of_nonneg_right ?_ (by linarith)
  exact expect_mono_tilt
    (fun q hq => ⟨tilt_nonneg (hδ q hq), (hν q hq).1.trans (hν q hq).2⟩)
    (fun q hq => ⟨(tilt_nonneg (hδ q hq)).trans (hν q hq).1, (hν q hq).2⟩)
    (fun q hq => (hν q hq).1) γ
    (monotone_hinge_Up (fun q hq => (Nat.prime_of_mem_primesBelow hq).pos) hp m (δ p))

/-- The admissibility condition `0 ≤ ν q ≤ q` of Smooth, from `tilt δ q ≤ ν q ≤ q`. -/
theorem nu_mem_of_tilt_le {δ : ℕ → ℝ} {Ps : Finset ℕ} (hδ : ∀ q ∈ Ps, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Ps, tilt δ q ≤ ν q ∧ ν q ≤ q) : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q :=
  fun q hq => ⟨(tilt_nonneg (hδ q hq)).trans (hν q hq).1, (hν q hq).2⟩

/-- **Exact tilts** (the landed checker never rounds `ν`): `ν := tilt δ` satisfies the tilt
hypothesis `tilt δ q ≤ ν q ≤ q` of every per-prime bound, for a certificate schedule
(`0 ≤ δ ≤ 1/2` at primes). -/
theorem tilt_mem_self {δ : ℕ → ℝ} (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) (p : ℕ) :
    ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ tilt δ q ∧ tilt δ q ≤ q := fun q hq =>
  ⟨le_rfl, tilt_le_self (hδ1 q (Nat.prime_of_mem_primesBelow hq))
    (Nat.prime_of_mem_primesBelow hq)⟩

/-- `δ q ≤ 1` below `p`, from a certificate schedule. -/
theorem delta_le_one_of_le_half {δ : ℕ → ℝ} (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) (p : ℕ) :
    ∀ q ∈ Nat.primesBelow p, δ q ≤ 1 := fun q hq =>
  (hδ1 q (Nat.prime_of_mem_primesBelow hq)).trans (by norm_num)

end MinModulus.CheckerMath
