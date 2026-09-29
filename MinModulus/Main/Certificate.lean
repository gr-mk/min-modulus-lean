import MinModulus.Smooth.Weights
import Mathlib.NumberTheory.PrimeCounting

/-!
# The numeric-certificate interface

STATUS: complete, no `sorry` (definitions plus small helper lemmas). Owned by the integration
agent (`Main`).

This file states the **single numeric fact** that the checker (`CheckerImpl` + `CheckerSound`)
must provide: a term of `Cert m X δ c T` for `m = 16000`, `X = 2·10^8`, and explicit
`δ c : ℕ → ℝ`, `T : ℝ`. `MinModulus.Main.not_covers_of_cert` (in `Main/Main.lean`) turns any
such term into the non-covering theorem for distinct moduli `≥ m`.

## The data
* `δ : ℕ → ℝ`, the distortion schedule, read at primes only: `δ p ∈ [0, 1/2]`, and `δ p = 1/2`
  for primes `p > X` (the tail choice).
* `tilt δ q = 1/(1 - δ q)`, the tilt `ν_q` of the law of the exponent of `q`.
* `c : ℕ → ℝ`, the per-prime costs (only `c p` for primes `p ≤ X` matter).
* `T : ℝ`, an upper bound for `∏_{q ≤ X prime} (1 + ν_q (3q - 1)/(q - 1)^2)`.

## The conditions
* (a) `delta_nonneg`, `delta_le_half`, `delta_tail`.
* (b) `loss_le`: for every prime `p ≤ X` and every **uniform** cap `N : ℕ`,
  `hingeLoss m δ p (fun _ => N) ≤ c p`, where
  `hingeLoss m δ p γ = E_γ[max 0 (U_p(s) - δ p) / (1 - δ p)]` is `Smooth.expect` over the exponent
  vectors `v` of **all** primes below `p` (`Nat.primesBelow p`), with tilts `tilt δ` and caps
  `γ`; `s = Smooth.smooth (Nat.primesBelow p) v = ∏_{q < p} q ^ v q`; `U_p = Smooth.Up p m`.
  (For `δ p = 0` the integrand is `U_p(s)`: the first moment.)
* (c) `prod_le`: `∏_{q ∈ Nat.primesLE X} tailFactor δ q ≤ T`, with
  `tailFactor δ q = 1 + tilt δ q * (3q - 1)/(q - 1)^2`.
* (d) `total_lt`: `∑_{p ∈ Nat.primesLE X} c p + T · 100/(189 X) < 1`.
* `two_pow_le`: `2^27 ≤ X` (needed by the tail bound `Tail.tail_bound_family_nu`, whose constant
  is `100/(189 X)`; at `X = 2·10^8` this is `≈ 2.6455·10^{-9} < 265/10^11`, see
  `total_lt_of_265`).

## What the integration proves from it (so the checker need not)
* Arbitrary caps: `Cert.loss_le_all` (monotone coupling in the caps, `Smooth.expect_mono_cap`).
* Arbitrary subsets of the primes below `p` (the primes of the actual system):
  `Main.expect_Up_mono_primes` in `Main/Main.lean`.
* `c p ≥ 0` (`Cert.cost_nonneg`) and `T ≥ 0` (`Cert.T_nonneg`).
-/

namespace MinModulus.Main

open Finset

/-- The tilt `ν_q = 1/(1 - δ_q)` of the exponent law at the prime `q`. -/
noncomputable def tilt (δ : ℕ → ℝ) (q : ℕ) : ℝ := 1 / (1 - δ q)

/-- The hinge loss at the prime `p` for the caps `γ`:
`E_γ[max 0 (U_p(s) - δ_p) / (1 - δ_p)]`, `s = ∏_{q < p prime} q ^ v_q`, where the `v_q` are
independent with the capped tilted law `Smooth.rho q (tilt δ q) (γ q)`. -/
noncomputable def hingeLoss (m : ℕ) (δ : ℕ → ℝ) (p : ℕ) (γ : ℕ → ℕ) : ℝ :=
  Smooth.expect (Nat.primesBelow p) (tilt δ) γ
    (fun v => max 0 (Smooth.Up p m (Smooth.smooth (Nat.primesBelow p) v) - δ p) / (1 - δ p))

/-- `1 + ν_q (3q - 1)/(q - 1)^2`, the uniform-in-the-cap bound for `E[(v_q + 1)^2]`
(`Smooth.expect1_sq_le`). -/
noncomputable def tailFactor (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  1 + tilt δ q * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2

/-- **The numeric certificate** for the minimum modulus `m`, with tail threshold `X`. -/
structure Cert (m X : ℕ) (δ : ℕ → ℝ) (c : ℕ → ℝ) (T : ℝ) : Prop where
  /-- The tail bound needs `X ≥ 2^27`. -/
  two_pow_le : 2 ^ 27 ≤ X
  /-- (a) -/
  delta_nonneg : ∀ p, p.Prime → 0 ≤ δ p
  /-- (a) -/
  delta_le_half : ∀ p, p.Prime → δ p ≤ 1 / 2
  /-- (a) the tail choice -/
  delta_tail : ∀ p, p.Prime → X < p → δ p = 1 / 2
  /-- (b) the per-prime costs, for every uniform cap `N` -/
  loss_le : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ, hingeLoss m δ p (fun _ => N) ≤ c p
  /-- (c) the product of the second-moment factors up to `X` -/
  prod_le : ∏ q ∈ Nat.primesLE X, tailFactor δ q ≤ T
  /-- (d) the total budget -/
  total_lt : ∑ p ∈ Nat.primesLE X, c p + T * (100 / (189 * (X : ℝ))) < 1

/-! ## Helper lemmas (proved) -/

theorem one_le_tilt {δ : ℕ → ℝ} {q : ℕ} (h0 : 0 ≤ δ q) (h1 : δ q ≤ 1 / 2) : 1 ≤ tilt δ q := by
  unfold tilt
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem tilt_le_two {δ : ℕ → ℝ} {q : ℕ} (h1 : δ q ≤ 1 / 2) : tilt δ q ≤ 2 := by
  unfold tilt
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem tilt_le_self {δ : ℕ → ℝ} {q : ℕ} (h1 : δ q ≤ 1 / 2) (hq : q.Prime) : tilt δ q ≤ q :=
  (tilt_le_two h1).trans (by exact_mod_cast hq.two_le)

/-- The tilts satisfy Smooth's standing hypothesis `0 ≤ ν q ≤ q` at primes. -/
theorem tilt_mem {δ : ℕ → ℝ} (hδ0 : ∀ q, q.Prime → 0 ≤ δ q)
    (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) {q : ℕ} (hq : q.Prime) : 0 ≤ tilt δ q ∧ tilt δ q ≤ q :=
  ⟨zero_le_one.trans (one_le_tilt (hδ0 q hq) (hδ1 q hq)), tilt_le_self (hδ1 q hq) hq⟩

theorem one_le_tailFactor {δ : ℕ → ℝ} {q : ℕ} (h0 : 0 ≤ δ q) (h1 : δ q ≤ 1 / 2) (hq : 1 ≤ q) :
    1 ≤ tailFactor δ q := by
  unfold tailFactor
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have : 0 ≤ tilt δ q * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 :=
    div_nonneg (mul_nonneg (zero_le_one.trans (one_le_tilt h0 h1)) (by linarith)) (sq_nonneg _)
  linarith

/-- `hingeLoss ≥ 0`. -/
theorem hingeLoss_nonneg {m : ℕ} {δ : ℕ → ℝ} (hδ0 : ∀ q, q.Prime → 0 ≤ δ q)
    (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) {p : ℕ} (hp : p.Prime) (γ : ℕ → ℕ) :
    0 ≤ hingeLoss m δ p γ := by
  have h1 : 0 < 1 - δ p := by linarith [hδ1 p hp]
  unfold hingeLoss
  exact Smooth.expect_nonneg (fun q hq => tilt_mem hδ0 hδ1 (Nat.prime_of_mem_primesBelow hq))
    fun v _ => div_nonneg (le_max_left _ _) h1.le

/-- `hingeLoss` is monotone in the caps (monotone coupling). -/
theorem hingeLoss_mono_cap {m : ℕ} {δ : ℕ → ℝ} (hδ0 : ∀ q, q.Prime → 0 ≤ δ q)
    (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) {p : ℕ} (hp : p.Prime) {γ γ' : ℕ → ℕ}
    (hγ : ∀ q ∈ Nat.primesBelow p, γ q ≤ γ' q) :
    hingeLoss m δ p γ ≤ hingeLoss m δ p γ' := by
  have h1 : 0 < 1 - δ p := by linarith [hδ1 p hp]
  unfold hingeLoss
  refine Smooth.expect_mono_cap (fun q hq => tilt_mem hδ0 hδ1 (Nat.prime_of_mem_primesBelow hq))
    hγ fun v w hvw => ?_
  exact div_le_div_of_nonneg_right (max_le_max le_rfl (sub_le_sub_right
    (Smooth.monotone_Up_smooth hp.one_lt m (fun q hq => (Nat.prime_of_mem_primesBelow hq).pos)
      hvw) _)) h1.le

/-- (b) for **all** caps, from (b) for uniform caps. -/
theorem Cert.loss_le_all {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert m X δ c T) {p : ℕ}
    (hp : p.Prime) (hpX : p ≤ X) (γ : ℕ → ℕ) : hingeLoss m δ p γ ≤ c p :=
  (hingeLoss_mono_cap hc.delta_nonneg hc.delta_le_half hp fun _ hq =>
    le_sup (f := γ) hq).trans (hc.loss_le p hp hpX ((Nat.primesBelow p).sup γ))

/-- The costs of a certificate are nonnegative (a consequence of (b)). -/
theorem Cert.cost_nonneg {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert m X δ c T) {p : ℕ}
    (hp : p.Prime) (hpX : p ≤ X) : 0 ≤ c p :=
  (hingeLoss_nonneg hc.delta_nonneg hc.delta_le_half hp _).trans (hc.loss_le p hp hpX 0)

/-- `T ≥ 0` for a certificate. -/
theorem Cert.T_nonneg {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert m X δ c T) : 0 ≤ T :=
  (prod_nonneg fun q hq => zero_le_one.trans (one_le_tailFactor
    (hc.delta_nonneg q (Nat.prime_of_mem_primesLE hq))
    (hc.delta_le_half q (Nat.prime_of_mem_primesLE hq))
    (Nat.prime_of_mem_primesLE hq).one_lt.le)).trans hc.prod_le

/-- Helper for the checker: condition (d) at `X = 2·10^8` follows from the rounder form
`∑ c + T · 265/10^11 < 1` (for `T ≥ 0`). -/
theorem total_lt_of_265 {S T : ℝ} (hT : 0 ≤ T) (h : S + T * (265 / 10 ^ 11) < 1) :
    S + T * (100 / (189 * ((2 * 10 ^ 8 : ℕ) : ℝ))) < 1 := by
  have : T * (100 / (189 * ((2 * 10 ^ 8 : ℕ) : ℝ))) ≤ T * (265 / 10 ^ 11) :=
    mul_le_mul_of_nonneg_left (by norm_num) hT
  linarith

end MinModulus.Main
