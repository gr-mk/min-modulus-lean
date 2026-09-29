import MinModulus.CheckerMath.HingeTilt

/-!
# CheckerMath: the θ-moment bounds (primes `2·10^5 < p ≤ 2·10^8`)

STATUS: complete, no `sorry`. Owned by the CheckerMath (first moment / moments / glue) agent.

For `0 < δ_p < 1` and `θ > 1`, pointwise `(U - δ_p)^+ ≤ c_θ(δ_p) U^θ`, `U_p(s) ≤ τ(s)/(p-1)`, and
`E[τ(s)^θ] = Π_q E[(v_q+1)^θ]`, so for **every** cap `γ`

  `hingeLoss m δ p γ ≤ c_θ(δ_p) · (Π_{q<p} B_q) / ((p-1)^θ (1 - δ_p))`

as soon as `B_q ≥ E_γ[(v_q+1)^θ]` for every cap (with the tilts `ν_q ≥ tilt δ q`).
Every constant may be replaced by a rational upper bound (`C ≥ c_θ(δ_p)`, `L ≤ (p-1)^θ`).

Main results:
* `hingeLoss_le_moment` : the general statement (any real `θ > 1`);
* `hingeLoss_le_moment_two`, `hingeLoss_le_moment_three`, `hingeLoss_le_moment_five_halves` :
  `θ = 2, 3, 5/2` with side conditions that are polynomial inequalities between reals
  (rational once the data are rational):
  - `θ = 2` : `1 ≤ 4 δ_p C`, `L ≤ (p-1)^2`;
  - `θ = 3` : `4 ≤ 27 δ_p² C`, `L ≤ (p-1)^3`;
  - `θ = 5/2` : `C ≥ c_{5/2}(δ_p)` (discharge with `ctheta_five_halves_le_mul`:
    `C = a·b`, `a ≥ 6/(25 δ)`, `b ≥ 0`, `b² ≥ 3/(5δ)`, or with `Smooth.ctheta_five_halves_le`)
    and `L ≤ (p-1)^{5/2}` (discharge with `le_rpow_five_halves_of_sq_le`: `L = y² r`,
    `r² ≤ y ≤ p - 1`, or with `Smooth.le_rpow_five_halves_iff`).
* per-prime factors `B_q`, uniform in the cap:
  - `expect1_sq_le_of_le`, `expect1_cube_le_of_le` : closed forms `1 + ν'(3Q-1)/(Q-1)²`,
    `1 + ν'(7Q²-2Q+1)/(Q-1)³` evaluated at any `Q ≤ q` (`1 < Q`) and any `ν' ≥ ν`
    (so one value serves a whole block of primes `q ≥ Q` with a common tilt bound);
  - `expect1_five_halves_le_sub` : **the CheckerImpl form for `θ = 5/2`**
    `E_γ[(v+1)^{5/2}] ≤ 1 + ν (1 - 1/q) (q(7q²-2q+1)/(q-1)⁴ - Σ_{a=1}^{A} q^{-a}((a+1)³ - (a+1)² s(a+1)))`
    for any `A` and any `s` with `s(a+1) ≥ 0`, `a + 1 ≤ s(a+1)²` (`1 ≤ a ≤ A`);
    also `Smooth.expect1_five_halves_le` (the rigcert ratio-test form);
  - `expect1_le_of_le_of_le` : `E_{q,ν,γ}[g] ≤ E_{Q,ν',γ}[g]` for monotone `g`, `0 < Q ≤ q`,
    `0 ≤ ν ≤ ν'` (antitone in the prime, monotone in the tilt).
* closed-form monotonicity: `sqFactor_anti`, `cubeFactor_anti`; `1 ≤ E_γ[(v+1)^θ]`
  (`one_le_expect1_rpow`, `one_le_expect1_pow`), so every `B q` is `≥ 1` (product glue).
* **block forms** mirroring `CheckerImpl.blockCost` (a prime `p` in a block starting at
  `P ≤ p`, with `Π_{q<p} B q ≤ ET`): `hingeLoss_le_moment_two_block` (`C·ET/((P-1)²(1-δ_p))`),
  `hingeLoss_le_moment_three_block` (`C·ET/((P-1)³(1-δ_p))`),
  `hingeLoss_le_moment_five_halves_block` (`C·ET/((P-1)² r (1-δ_p))`, `0 < r`, `r² ≤ P-1`).

* **alignment with the landed `CheckerImpl`** (`δ = dn/D`, `D = 10^9`, exact tilt
  `ν = D/(D - dn)`): `sqFactor_eq_ratio`, `cubeFactor_eq_ratio` (the rationals rounded by
  `fac2`, `fac3`); `expect1_sq_le_ratio`, `expect1_cube_le_ratio`, `expect1_five_halves_le_ratio`
  (`E_γ[(v+1)^θ] ≤` the rational rounded by `fac2`/`fac3`/`fac25` at the block start `Q ≤ q`);
  `hingeLoss_le_blockVal_two`, `_three`, `_five_halves` (the three candidates `k2`, `k3`, `k25`
  of `blockVal`, in exactly its arithmetic form).

Remark. `Main.hingeLoss` has no cap `min(1, U)`, so only the unconstrained constant
`c_θ(δ) = max_{u ≥ δ} (u-δ)/u^θ` is available (rigcert's branch `cth = 1 - d`, used when
`θδ/(θ-1) > 1`, is not). For `θ ∈ {2, 5/2, 3}` and `δ ≤ 0.45` the maximiser `θδ/(θ-1) < 1`, so
the two constants coincide there.
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth MinModulus.Main

/-! ### The general θ-moment bound -/

/-- **θ-moment bound, certificate form.** For `0 < δ_p < 1`, tilt upper bounds
`tilt δ q ≤ ν q ≤ q` below `p`, `θ > 1`, per-prime bounds `B q ≥ E_γ[(v_q + 1)^θ]` (every cap),
`C ≥ c_θ(δ_p)` and `0 < L ≤ (p-1)^θ`: for every cap `γ`,
`hingeLoss m δ p γ ≤ C · Π_{q<p} B q / (L (1 - δ_p))`. -/
theorem hingeLoss_le_moment {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hδp0 : 0 < δ p)
    (hδp1 : δ p < 1) (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) {θ : ℝ} (hθ : 1 < θ) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ θ) ≤ B q)
    {C L : ℝ} (hC : ctheta θ (δ p) ≤ C) (hL0 : 0 < L) (hL : L ≤ ((p : ℝ) - 1) ^ θ)
    (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * (∏ q ∈ Nat.primesBelow p, B q) / (L * (1 - δ p)) := by
  have hνm := nu_mem_of_tilt_le hδ hν
  have h1t : 0 < 1 - δ p := by linarith
  have h1 := hingeLoss_le_of_tilt_le (m := m) hp.one_lt hδp1 hδ hν γ
  have h2 := expect_hinge_Up_le_prod (fun q hq => Nat.prime_of_mem_primesBelow hq) hνm γ
    hp.one_lt m hδp0 hθ B (fun q hq => hB q hq (γ q))
  have hB0 : 0 ≤ ∏ q ∈ Nat.primesBelow p, B q := prod_nonneg fun q hq =>
    (expect1_nonneg (hνm q hq).1 (hνm q hq).2 fun a _ => Real.rpow_nonneg (by positivity) θ).trans
      (hB q hq 0)
  have hc0 : 0 ≤ ctheta θ (δ p) := (ctheta_pos hδp0 hθ).le
  have h3 : ctheta θ (δ p) / ((p : ℝ) - 1) ^ θ ≤ C / L :=
    div_le_div₀ (hc0.trans hC) hC hL0 hL
  calc hingeLoss m δ p γ
      ≤ expect (Nat.primesBelow p) ν γ
          (fun v => max 0 (Up p m (smooth (Nat.primesBelow p) v) - δ p)) / (1 - δ p) := h1
    _ ≤ (ctheta θ (δ p) / ((p : ℝ) - 1) ^ θ * ∏ q ∈ Nat.primesBelow p, B q) / (1 - δ p) :=
        div_le_div_of_nonneg_right h2 h1t.le
    _ ≤ (C / L * ∏ q ∈ Nat.primesBelow p, B q) / (1 - δ p) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hB0) h1t.le
    _ = C * (∏ q ∈ Nat.primesBelow p, B q) / (L * (1 - δ p)) := by
        field_simp

/-! ### θ = 2 and θ = 3 -/

theorem rpow_two_eq (y : ℝ) : y ^ (2 : ℝ) = y ^ 2 := by norm_cast

theorem rpow_three_eq (y : ℝ) : y ^ (3 : ℝ) = y ^ 3 := by norm_cast

/-- **θ = 2** (rational side conditions): `1 ≤ 4 δ_p C`, `0 < L ≤ (p-1)²`, and
`B q ≥ E_γ[(v_q + 1)²]` for every cap. -/
theorem hingeLoss_le_moment_two {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hδp0 : 0 < δ p)
    (hδp1 : δ p < 1) (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ B q)
    {C L : ℝ} (hC : 1 ≤ 4 * δ p * C) (hL0 : 0 < L) (hL : L ≤ ((p : ℝ) - 1) ^ 2)
    (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * (∏ q ∈ Nat.primesBelow p, B q) / (L * (1 - δ p)) := by
  refine hingeLoss_le_moment hp hδp0 hδp1 hδ hν (θ := 2) (by norm_num) B
    (fun q hq γ => by simpa only [rpow_two_eq] using hB q hq γ) ?_ hL0 (by rwa [rpow_two_eq]) γ
  rw [ctheta_two hδp0, div_le_iff₀ (by positivity)]
  linarith

/-- **θ = 3** (rational side conditions): `4 ≤ 27 δ_p² C`, `0 < L ≤ (p-1)³`, and
`B q ≥ E_γ[(v_q + 1)³]` for every cap. -/
theorem hingeLoss_le_moment_three {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hδp0 : 0 < δ p)
    (hδp1 : δ p < 1) (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 3) ≤ B q)
    {C L : ℝ} (hC : 4 ≤ 27 * δ p ^ 2 * C) (hL0 : 0 < L) (hL : L ≤ ((p : ℝ) - 1) ^ 3)
    (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * (∏ q ∈ Nat.primesBelow p, B q) / (L * (1 - δ p)) := by
  refine hingeLoss_le_moment hp hδp0 hδp1 hδ hν (θ := 3) (by norm_num) B
    (fun q hq γ => by simpa only [rpow_three_eq] using hB q hq γ) ?_ hL0
    (by rwa [rpow_three_eq]) γ
  rw [ctheta_three hδp0, div_le_iff₀ (by positivity)]
  linarith

/-! ### θ = 5/2 -/

/-- **θ = 5/2**: `C ≥ c_{5/2}(δ_p)`, `0 < L ≤ (p-1)^{5/2}`, `B q ≥ E_γ[(v_q + 1)^{5/2}]`. -/
theorem hingeLoss_le_moment_five_halves {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hδp0 : 0 < δ p)
    (hδp1 : δ p < 1) (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Nat.primesBelow p, ∀ γ,
      expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤ B q)
    {C L : ℝ} (hC : ctheta (5 / 2) (δ p) ≤ C) (hL0 : 0 < L)
    (hL : L ≤ ((p : ℝ) - 1) ^ (5 / 2 : ℝ)) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * (∏ q ∈ Nat.primesBelow p, B q) / (L * (1 - δ p)) :=
  hingeLoss_le_moment hp hδp0 hδp1 hδ hν (by norm_num) B hB hC hL0 hL γ

/-- Rational certificate for `c_{5/2}(t) = (6/(25 t))·√(3/(5 t))`: if `a ≥ 6/(25 t)`, `b ≥ 0` and
`b² ≥ 3/(5 t)`, then `c_{5/2}(t) ≤ a · b`. -/
theorem ctheta_five_halves_le_mul {t : ℝ} (ht : 0 < t) {a b : ℝ} (ha : 6 / (25 * t) ≤ a)
    (hb0 : 0 ≤ b) (hb : 3 / (5 * t) ≤ b ^ 2) : ctheta (5 / 2) t ≤ a * b := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  refine ctheta_five_halves_le ht (mul_nonneg ha0 hb0) ?_
  have h1 : (6 / (25 * t)) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) ha 2
  have h2 : (6 / (25 * t)) ^ 2 * (3 / (5 * t)) ≤ a ^ 2 * b ^ 2 :=
    mul_le_mul h1 hb (by positivity) (sq_nonneg a)
  have h3 : (2 * t / 3) ^ 2 = (6 / (25 * t)) ^ 2 * (3 / (5 * t)) * (5 * t / 3) ^ 5 := by
    field_simp
    ring
  rw [h3, mul_pow]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- Rational lower bound for `z^{5/2}`: if `r² ≤ y` and `y ≤ z`, then `y² r ≤ z^{5/2}`
(e.g. `y = P - 1` for a block start `P ≤ p`, `z = p - 1`, `r = ⌊√(P-1)·2^32⌋/2^32`). -/
theorem le_rpow_five_halves_of_sq_le {r y z : ℝ} (hry : r ^ 2 ≤ y) (hyz : y ≤ z) :
    y ^ 2 * r ≤ z ^ (5 / 2 : ℝ) := by
  have hy : 0 ≤ y := (sq_nonneg r).trans hry
  have h1 : y ^ 2 * r ≤ y ^ (5 / 2 : ℝ) := by
    rw [rpow_five_halves hy]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg y)
    exact Real.le_sqrt_of_sq_le hry
  exact h1.trans (Real.rpow_le_rpow hy hyz (by norm_num))

/-! ### Per-prime factors `B_q`: monotonicity in the prime and in the tilt -/

/-- `E_{q,ν,γ}[g]` is antitone in the prime `q` and monotone in the tilt `ν`, for monotone `g`:
for `0 < Q ≤ q` and `0 ≤ ν ≤ ν'`, `E_{q,ν,γ}[g] ≤ E_{Q,ν',γ}[g]`. -/
theorem expect1_le_of_le_of_le {q Q : ℕ} (hQ : 0 < Q) (hQq : Q ≤ q) {ν ν' : ℝ} (hν : 0 ≤ ν)
    (hνν' : ν ≤ ν') {g : ℕ → ℝ} (hg : Monotone g) (γ : ℕ) :
    expect1 q ν γ g ≤ expect1 Q ν' γ g := by
  refine le_trans ?_ (expect1_mono_tilt hνν' hg Q γ)
  rw [expect1_eq_geom, expect1_eq_geom]
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hx : ((q : ℝ))⁻¹ ≤ ((Q : ℝ))⁻¹ := inv_anti₀ hQ' (by exact_mod_cast hQq)
  have hx0 : 0 ≤ ((q : ℝ))⁻¹ := by positivity
  have : ∑ r ∈ range γ, ((q : ℝ)⁻¹) ^ (r + 1) * (g (r + 1) - g r) ≤
      ∑ r ∈ range γ, ((Q : ℝ)⁻¹) ^ (r + 1) * (g (r + 1) - g r) :=
    sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx _)
      (sub_nonneg.2 (hg (Nat.le_succ r)))
  have := mul_le_mul_of_nonneg_left this hν
  linarith

theorem monotone_add_one_pow (k : ℕ) : Monotone (fun a : ℕ => ((a : ℝ) + 1) ^ k) := by
  intro a b hab
  have : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  exact pow_le_pow_left₀ (by positivity) this k

theorem monotone_add_one_rpow {θ : ℝ} (hθ : 0 ≤ θ) :
    Monotone (fun a : ℕ => ((a : ℝ) + 1) ^ θ) := by
  intro a b hab
  have : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  exact Real.rpow_le_rpow (by positivity) this hθ

/-- **θ = 2, block form**: for `1 < Q ≤ q`, `0 ≤ ν ≤ ν'` and every cap,
`E_{q,ν,γ}[(v+1)²] ≤ 1 + ν' (3Q - 1)/(Q - 1)²`. -/
theorem expect1_sq_le_of_le {q Q : ℕ} (hQ : 1 < Q) (hQq : Q ≤ q) {ν ν' : ℝ} (hν : 0 ≤ ν)
    (hνν' : ν ≤ ν') (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ 1 + ν' * (3 * Q - 1) / ((Q : ℝ) - 1) ^ 2 :=
  (expect1_le_of_le_of_le (by omega) hQq hν hνν' (monotone_add_one_pow 2) γ).trans
    (expect1_sq_le hQ (hν.trans hνν') γ)

/-- **θ = 3, block form**: for `1 < Q ≤ q`, `0 ≤ ν ≤ ν'` and every cap,
`E_{q,ν,γ}[(v+1)³] ≤ 1 + ν' (7Q² - 2Q + 1)/(Q - 1)³`. -/
theorem expect1_cube_le_of_le {q Q : ℕ} (hQ : 1 < Q) (hQq : Q ≤ q) {ν ν' : ℝ} (hν : 0 ≤ ν)
    (hνν' : ν ≤ ν') (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 3) ≤
      1 + ν' * (7 * (Q : ℝ) ^ 2 - 2 * Q + 1) / ((Q : ℝ) - 1) ^ 3 :=
  (expect1_le_of_le_of_le (by omega) hQq hν hνν' (monotone_add_one_pow 3) γ).trans
    (expect1_cube_le hQ (hν.trans hνν') γ)

/-- **θ = 5/2, CheckerImpl form**, uniform in the cap. For `q > 1`, `0 ≤ ν ≤ q`, any `A` and any
`s` with `s(a+1) ≥ 0` and `a + 1 ≤ s(a+1)²` for `1 ≤ a ≤ A` (i.e. `s(a+1) ≥ √(a+1)`):
`E_γ[(v+1)^{5/2}] ≤ 1 + ν (1 - 1/q) · W`, where
`W = q(7q² - 2q + 1)/(q - 1)⁴ - Σ_{a=1}^{A} q^{-a} ((a+1)³ - (a+1)² s(a+1))`.
(`q(7q²-2q+1)/(q-1)⁴ = Σ_{a≥1} q^{-a}((a+1)³ - 1)`; the bound uses `(a+1)^{5/2} ≤ (a+1)² s(a+1)`
for `a ≤ A` and `(a+1)^{5/2} ≤ (a+1)³` beyond.) -/
theorem expect1_five_halves_le_sub {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) (hνq : ν ≤ q)
    (A : ℕ) (s : ℕ → ℝ) (hs0 : ∀ a ∈ Icc 1 A, 0 ≤ s (a + 1))
    (hs : ∀ a ∈ Icc 1 A, (a : ℝ) + 1 ≤ s (a + 1) ^ 2) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤
      1 + ν * (1 - (q : ℝ)⁻¹) *
        ((q : ℝ) * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 4 -
          ∑ a ∈ Icc 1 A, ((q : ℝ)⁻¹) ^ a *
            (((a : ℝ) + 1) ^ 3 - ((a : ℝ) + 1) ^ 2 * s (a + 1))) := by
  classical
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  set x : ℝ := (q : ℝ)⁻¹ with hx
  set k : ℕ → ℝ := fun a => ((a : ℝ) + 1) ^ 3 - ((a : ℝ) + 1) ^ 2 * s (a + 1) with hk
  set γ' := max γ (A + 1) with hγ'
  have hAγ' : A < γ' := lt_of_lt_of_le (Nat.lt_succ_self A) (le_max_right _ _)
  -- step 1: raise the cap
  have h1 : expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤
      expect1 q ν γ' (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) :=
    expect1_mono_cap hν (monotone_add_one_rpow (by norm_num)) (le_max_left _ _)
  -- step 2: pointwise majorant
  have h2 : expect1 q ν γ' (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤
      expect1 q ν γ' (fun a => ((a : ℝ) + 1) ^ 3 - (if a ∈ Icc 1 A then k a else 0)) := by
    refine expect1_mono hν hνq fun a _ => ?_
    have hy : (1 : ℝ) ≤ (a : ℝ) + 1 := by
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    split_ifs with ha
    · simp only [hk, sub_sub_cancel]
      rw [rpow_five_halves (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact Real.sqrt_le_iff.2 ⟨hs0 a ha, hs a ha⟩
    · rw [sub_zero, ← rpow_three_eq]
      exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  -- step 3: split the expectation
  have h3 : expect1 q ν γ' (fun a => ((a : ℝ) + 1) ^ 3 - (if a ∈ Icc 1 A then k a else 0)) =
      expect1 q ν γ' (fun a => ((a : ℝ) + 1) ^ 3) -
        ∑ a ∈ Icc 1 A, ν * x ^ a * (1 - x) * k a := by
    unfold expect1
    simp_rw [mul_sub, sum_sub_distrib]
    congr 1
    simp_rw [mul_ite, mul_zero]
    rw [sum_ite_mem, inter_eq_right.2]
    · refine sum_congr rfl fun a ha => ?_
      rw [mem_Icc] at ha
      rw [rho_of_pos_of_lt (by omega) (by omega), hx]
      ring
    · intro a ha
      rw [mem_Icc] at ha
      exact mem_range.2 (by omega)
  -- step 4: the cube
  have h4 := expect1_cube_le hq hν γ'
  have e1 : ν * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 =
      ν * (1 - x) * ((q : ℝ) * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 4) := by
    rw [hx]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hq1' : (q : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  have e2 : ∑ a ∈ Icc 1 A, ν * x ^ a * (1 - x) * k a =
      ν * (1 - x) * ∑ a ∈ Icc 1 A, x ^ a * k a := by
    rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  calc expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ))
      ≤ expect1 q ν γ' (fun a => ((a : ℝ) + 1) ^ 3) -
          ∑ a ∈ Icc 1 A, ν * x ^ a * (1 - x) * k a := by linarith
    _ ≤ 1 + ν * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 -
          ∑ a ∈ Icc 1 A, ν * x ^ a * (1 - x) * k a := by linarith
    _ = 1 + ν * (1 - x) * ((q : ℝ) * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 4 -
          ∑ a ∈ Icc 1 A, x ^ a * k a) := by
        linear_combination e1 - e2

/-- **θ = 5/2, block form** of `expect1_five_halves_le_sub`: the bound computed at `(Q, ν')`
holds at every prime `q ≥ Q` with tilt `0 ≤ ν ≤ ν'` (and `ν' ≤ Q`). -/
theorem expect1_five_halves_le_sub_of_le {q Q : ℕ} (hQ : 1 < Q) (hQq : Q ≤ q) {ν ν' : ℝ}
    (hν : 0 ≤ ν) (hνν' : ν ≤ ν') (hν'Q : ν' ≤ Q) (A : ℕ) (s : ℕ → ℝ)
    (hs0 : ∀ a ∈ Icc 1 A, 0 ≤ s (a + 1)) (hs : ∀ a ∈ Icc 1 A, (a : ℝ) + 1 ≤ s (a + 1) ^ 2)
    (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤
      1 + ν' * (1 - (Q : ℝ)⁻¹) *
        ((Q : ℝ) * (7 * (Q : ℝ) ^ 2 - 2 * Q + 1) / ((Q : ℝ) - 1) ^ 4 -
          ∑ a ∈ Icc 1 A, ((Q : ℝ)⁻¹) ^ a *
            (((a : ℝ) + 1) ^ 3 - ((a : ℝ) + 1) ^ 2 * s (a + 1))) :=
  (expect1_le_of_le_of_le (by omega) hQq hν hνν' (monotone_add_one_rpow (by norm_num)) γ).trans
    (expect1_five_halves_le_sub hQ (hν.trans hνν') hν'Q A s hs0 hs γ)

/-! ### Closed-form factors are antitone in the prime -/

/-- `(3q - 1)/(q - 1)²` is antitone on `q ≥ 2`. -/
theorem sqFactor_anti {Q q : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) :
    (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 ≤ (3 * (Q : ℝ) - 1) / ((Q : ℝ) - 1) ^ 2 := by
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQq' : (Q : ℝ) ≤ q := by exact_mod_cast hQq
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hQq') (by nlinarith : (0 : ℝ) ≤ 3 * ((Q : ℝ) - 1) * ((q : ℝ) - 1) + 2 * ((Q : ℝ) - 1) + 2 * ((q : ℝ) - 1))]

/-- `(7q² - 2q + 1)/(q - 1)³` is antitone on `q ≥ 2`. -/
theorem cubeFactor_anti {Q q : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) :
    (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 ≤
      (7 * (Q : ℝ) ^ 2 - 2 * Q + 1) / ((Q : ℝ) - 1) ^ 3 := by
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQq' : (Q : ℝ) ≤ q := by exact_mod_cast hQq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hQ1 : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
  rw [div_le_div_iff₀ (pow_pos hq1 3) (pow_pos hQ1 3)]
  -- with a = Q - 1, b = q - 1 ≥ a ≥ 1:
  -- (7Q²-2Q+1)(q-1)³ - (7q²-2q+1)(Q-1)³ = (b - a)·(polynomial with positive coefficients)
  set a : ℝ := (Q : ℝ) - 1 with ha
  set b : ℝ := (q : ℝ) - 1 with hb
  have hQa : (Q : ℝ) = a + 1 := by rw [ha]; ring
  have hqb : (q : ℝ) = b + 1 := by rw [hb]; ring
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith
  rw [hQa, hqb]
  have key : (7 * (a + 1) ^ 2 - 2 * (a + 1) + 1) * b ^ 3 - (7 * (b + 1) ^ 2 - 2 * (b + 1) + 1) * a ^ 3 =
      (b - a) * (7 * a ^ 2 * b ^ 2 + 12 * a * b * (a + b) + 6 * (a ^ 2 + a * b + b ^ 2)) := by
    ring
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hpos : 0 ≤ (b - a) * (7 * a ^ 2 * b ^ 2 + 12 * a * b * (a + b) + 6 * (a ^ 2 + a * b + b ^ 2)) := by
    refine mul_nonneg (by linarith) ?_
    have h1 : 0 ≤ 7 * a ^ 2 * b ^ 2 := by positivity
    have h2 : 0 ≤ 12 * a * b * (a + b) := by
      have := mul_nonneg hab0 (add_nonneg ha0 hb0)
      nlinarith
    have h3 : 0 ≤ 6 * (a ^ 2 + a * b + b ^ 2) := by nlinarith [sq_nonneg a, sq_nonneg b]
    linarith
  nlinarith [key, hpos]

/-! ### Every per-prime factor is `≥ 1` -/

theorem one_le_expect1_rpow {q : ℕ} {ν : ℝ} (hν : 0 ≤ ν) (hνq : ν ≤ q) {θ : ℝ} (hθ : 0 ≤ θ)
    (γ : ℕ) : 1 ≤ expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ θ) := by
  have h := expect1_mono (q := q) (γ := γ) hν hνq (f := fun _ => (1 : ℝ))
    (g := fun a => ((a : ℝ) + 1) ^ θ) fun a _ =>
      Real.one_le_rpow (by have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith) hθ
  rwa [expect1_const] at h

theorem one_le_expect1_pow {q : ℕ} {ν : ℝ} (hν : 0 ≤ ν) (hνq : ν ≤ q) (k γ : ℕ) :
    1 ≤ expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ k) := by
  have h := expect1_mono (q := q) (γ := γ) hν hνq (f := fun _ => (1 : ℝ))
    (g := fun a => ((a : ℝ) + 1) ^ k) fun a _ =>
      one_le_pow₀ (by have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)
  rwa [expect1_const] at h

/-! ### Block forms (mirroring `CheckerImpl.blockCost`) -/

/-- **θ = 2, block form.** A prime `p` in a block starting at `P` (`2 ≤ P ≤ p`), with
`Π_{q<p} B q ≤ ET`: `hingeLoss m δ p γ ≤ C · ET / ((P-1)² (1 - δ_p))` for `1 ≤ 4 δ_p C`. -/
theorem hingeLoss_le_moment_two_block {m p P : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hP : 2 ≤ P)
    (hPp : P ≤ p) (hδp0 : 0 < δ p) (hδp1 : δ p < 1) (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1)
    {ν : ℕ → ℝ} (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ B q)
    {ET : ℝ} (hET : ∏ q ∈ Nat.primesBelow p, B q ≤ ET) {C : ℝ} (hC : 1 ≤ 4 * δ p * C)
    (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * ET / (((P : ℝ) - 1) ^ 2 * (1 - δ p)) := by
  have hP1 : (0 : ℝ) < (P : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hPp' : (P : ℝ) - 1 ≤ (p : ℝ) - 1 := by
    have : (P : ℝ) ≤ p := by exact_mod_cast hPp
    linarith
  have hC0 : 0 ≤ C := by
    by_contra h
    have : 4 * δ p * C < 0 := mul_neg_of_pos_of_neg (by positivity) (not_le.1 h)
    linarith
  refine (hingeLoss_le_moment_two hp hδp0 hδp1 hδ hν B hB hC (pow_pos hP1 2)
    (pow_le_pow_left₀ hP1.le hPp' 2) γ).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hET hC0)
    (mul_pos (pow_pos hP1 2) (by linarith)).le

/-- **θ = 3, block form**: `hingeLoss m δ p γ ≤ C · ET / ((P-1)³ (1 - δ_p))` for
`4 ≤ 27 δ_p² C`. -/
theorem hingeLoss_le_moment_three_block {m p P : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hP : 2 ≤ P)
    (hPp : P ≤ p) (hδp0 : 0 < δ p) (hδp1 : δ p < 1) (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1)
    {ν : ℕ → ℝ} (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 3) ≤ B q)
    {ET : ℝ} (hET : ∏ q ∈ Nat.primesBelow p, B q ≤ ET) {C : ℝ} (hC : 4 ≤ 27 * δ p ^ 2 * C)
    (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * ET / (((P : ℝ) - 1) ^ 3 * (1 - δ p)) := by
  have hP1 : (0 : ℝ) < (P : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hPp' : (P : ℝ) - 1 ≤ (p : ℝ) - 1 := by
    have : (P : ℝ) ≤ p := by exact_mod_cast hPp
    linarith
  have hC0 : 0 ≤ C := by
    by_contra h
    have : 27 * δ p ^ 2 * C < 0 := mul_neg_of_pos_of_neg (by positivity) (not_le.1 h)
    linarith
  refine (hingeLoss_le_moment_three hp hδp0 hδp1 hδ hν B hB hC (pow_pos hP1 3)
    (pow_le_pow_left₀ hP1.le hPp' 3) γ).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hET hC0)
    (mul_pos (pow_pos hP1 3) (by linarith)).le

/-- **θ = 5/2, block form**: for `0 < r` with `r² ≤ P - 1` and `C ≥ c_{5/2}(δ_p)`,
`hingeLoss m δ p γ ≤ C · ET / ((P-1)² r (1 - δ_p))`. -/
theorem hingeLoss_le_moment_five_halves_block {m p P : ℕ} {δ : ℕ → ℝ} (hp : p.Prime)
    (hP : 2 ≤ P) (hPp : P ≤ p) (hδp0 : 0 < δ p) (hδp1 : δ p < 1)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Nat.primesBelow p, ∀ γ,
      expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤ B q)
    {ET : ℝ} (hET : ∏ q ∈ Nat.primesBelow p, B q ≤ ET) {C : ℝ}
    (hC : ctheta (5 / 2) (δ p) ≤ C) {r : ℝ} (hr0 : 0 < r) (hr : r ^ 2 ≤ (P : ℝ) - 1)
    (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * ET / (((P : ℝ) - 1) ^ 2 * r * (1 - δ p)) := by
  have hP1 : (0 : ℝ) < (P : ℝ) - 1 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hPp' : (P : ℝ) - 1 ≤ (p : ℝ) - 1 := by
    have : (P : ℝ) ≤ p := by exact_mod_cast hPp
    linarith
  have hC0 : 0 ≤ C := (ctheta_pos hδp0 (by norm_num)).le.trans hC
  have hL0 : 0 < ((P : ℝ) - 1) ^ 2 * r := mul_pos (pow_pos hP1 2) hr0
  refine (hingeLoss_le_moment_five_halves hp hδp0 hδp1 hδ hν B hB hC hL0
    (le_rpow_five_halves_of_sq_le hr hPp') γ).trans ?_
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hET hC0)
    (mul_pos hL0 (by linarith)).le

/-! ### Alignment with `CheckerImpl.Moments` (`fac2`, `fac3`, `fac25`, `cTheta*`, `blockVal`)

The checker stores `δ = dn/D` (`D = DDEN = 10^9`) and uses the **exact** tilt
`ν = D/(D - dn)`. Each of its quantities rounds (once, upward) an exact rational; the lemmas
below state the bounds in exactly those rational forms, so that the code-level proof only needs
the rounding specifications (`ratUp_spec`, `cdiv_spec`, `mulUp_spec`, `Nat.sqrt_le'`, …). -/

/-- The rational rounded by `fac2 q dn`: `1 + ν(3q-1)/(q-1)² = (d + D(3q-1))/d`,
`d = (q-1)²(D-dn)`, `ν = D/(D-dn)`. -/
theorem sqFactor_eq_ratio {q dn D : ℕ} (hq : 2 ≤ q) (hdn : dn < D) :
    1 + (D : ℝ) / ((D : ℝ) - dn) * (3 * q - 1) / ((q : ℝ) - 1) ^ 2 =
      (((q : ℝ) - 1) ^ 2 * ((D : ℝ) - dn) + D * (3 * q - 1)) /
        (((q : ℝ) - 1) ^ 2 * ((D : ℝ) - dn)) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : (dn : ℝ) < D := by exact_mod_cast hdn
  have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (D : ℝ) - dn ≠ 0 := by linarith
  field_simp

/-- The rational rounded by `fac3 q dn`: `1 + ν(7q²-2q+1)/(q-1)³ = (d + D(7q²-2q+1))/d`,
`d = (q-1)³(D-dn)`. -/
theorem cubeFactor_eq_ratio {q dn D : ℕ} (hq : 2 ≤ q) (hdn : dn < D) :
    1 + (D : ℝ) / ((D : ℝ) - dn) * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 =
      (((q : ℝ) - 1) ^ 3 * ((D : ℝ) - dn) + D * (7 * (q : ℝ) ^ 2 - 2 * q + 1)) /
        (((q : ℝ) - 1) ^ 3 * ((D : ℝ) - dn)) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : (dn : ℝ) < D := by exact_mod_cast hdn
  have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (D : ℝ) - dn ≠ 0 := by linarith
  field_simp

/-- **`fac2`, exact form.** For `2 ≤ Q ≤ q` (`Q` a block start, or `Q = q`), tilts
`0 ≤ ν ≤ D/(D - dn)` and every cap: `E_{q,ν,γ}[(v+1)²] ≤ (d + D(3Q-1))/d`, `d = (Q-1)²(D-dn)`. -/
theorem expect1_sq_le_ratio {q Q dn D : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hdn : dn < D) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν ≤ (D : ℝ) / ((D : ℝ) - dn)) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 2) ≤
      (((Q : ℝ) - 1) ^ 2 * ((D : ℝ) - dn) + D * (3 * Q - 1)) /
        (((Q : ℝ) - 1) ^ 2 * ((D : ℝ) - dn)) := by
  rw [← sqFactor_eq_ratio hQ hdn]
  exact expect1_sq_le_of_le (by omega) hQq hν0 hν γ

/-- **`fac3`, exact form**: `E_{q,ν,γ}[(v+1)³] ≤ (d + D(7Q²-2Q+1))/d`, `d = (Q-1)³(D-dn)`. -/
theorem expect1_cube_le_ratio {q Q dn D : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hdn : dn < D) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν ≤ (D : ℝ) / ((D : ℝ) - dn)) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 3) ≤
      (((Q : ℝ) - 1) ^ 3 * ((D : ℝ) - dn) + D * (7 * (Q : ℝ) ^ 2 - 2 * Q + 1)) /
        (((Q : ℝ) - 1) ^ 3 * ((D : ℝ) - dn)) := by
  rw [← cubeFactor_eq_ratio hQ hdn]
  exact expect1_cube_le_of_le (by omega) hQq hν0 hν γ

/-- **`fac25`, exact form.** For `2 ≤ Q ≤ q`, `0 ≤ ν ≤ D/(D - dn) ≤ Q`, square-root upper bounds
`s(a+1) ≥ √(a+1)` (`1 ≤ a ≤ A`) and any `W ≥ Q(7Q²-2Q+1)/(Q-1)⁴ - Σ_{a=1}^{A} Q^{-a}((a+1)³ -
(a+1)² s(a+1))` (the checker's `s3 - fac25Sub`): `E_{q,ν,γ}[(v+1)^{5/2}] ≤ 1 + D(Q-1)W/((D-dn)Q)`
(`fac25 = ONE + cdiv (DDEN·(Q-1)·W) ((DDEN - dn)·Q)`). -/
theorem expect1_five_halves_le_ratio {q Q dn D : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hdn : dn < D)
    (hDQ : (D : ℝ) / ((D : ℝ) - dn) ≤ Q) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν ≤ (D : ℝ) / ((D : ℝ) - dn)) (A : ℕ) (s : ℕ → ℝ)
    (hs0 : ∀ a ∈ Icc 1 A, 0 ≤ s (a + 1)) (hs : ∀ a ∈ Icc 1 A, (a : ℝ) + 1 ≤ s (a + 1) ^ 2)
    {W : ℝ}
    (hW : (Q : ℝ) * (7 * (Q : ℝ) ^ 2 - 2 * Q + 1) / ((Q : ℝ) - 1) ^ 4 -
      ∑ a ∈ Icc 1 A, ((Q : ℝ)⁻¹) ^ a * (((a : ℝ) + 1) ^ 3 - ((a : ℝ) + 1) ^ 2 * s (a + 1)) ≤ W)
    (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤
      1 + D * ((Q : ℝ) - 1) * W / (((D : ℝ) - dn) * Q) := by
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : (dn : ℝ) < D := by exact_mod_cast hdn
  have hDd : (0 : ℝ) < (D : ℝ) - dn := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hν' : (0 : ℝ) ≤ (D : ℝ) / ((D : ℝ) - dn) := div_nonneg hD0 hDd.le
  have h1 := expect1_five_halves_le_sub_of_le (by omega) hQq hν0 hν hDQ A s hs0 hs γ
  have hcoef : 0 ≤ (D : ℝ) / ((D : ℝ) - dn) * (1 - (Q : ℝ)⁻¹) := by
    refine mul_nonneg hν' ?_
    have : (Q : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  have h2 := mul_le_mul_of_nonneg_left hW hcoef
  have e : (D : ℝ) / ((D : ℝ) - dn) * (1 - (Q : ℝ)⁻¹) * W =
      D * ((Q : ℝ) - 1) * W / (((D : ℝ) - dn) * Q) := by
    have hQ0 : (Q : ℝ) ≠ 0 := by positivity
    field_simp
  linarith

/-- **`blockVal`, θ = 2** (`k2 = cdiv (cTheta2 dn · ET2 · DDEN) ((B-1)²·(DDEN-dn)·ONE)`): a prime
`p ≥ B` of a block starting at `B`, `δ_p = dn/D > 0`, `Π_{q<p} B_q ≤ ET`, `C ≥ D/(4 dn)`
(`cTheta2 dn = ratUp DDEN (4 dn)`): `hingeLoss m δ p γ ≤ C · ET · D / ((B-1)² (D - dn))`. -/
theorem hingeLoss_le_blockVal_two {m p B dn D : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hB : 2 ≤ B)
    (hBp : B ≤ p) (hδp : δ p = (dn : ℝ) / D) (hdn0 : 0 < dn) (hdnD : dn < D)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (Bq : ℕ → ℝ)
    (hBq : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ Bq q)
    {ET : ℝ} (hET : ∏ q ∈ Nat.primesBelow p, Bq q ≤ ET) {C : ℝ}
    (hC : (D : ℝ) / (4 * dn) ≤ C) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * ET * D / (((B : ℝ) - 1) ^ 2 * ((D : ℝ) - dn)) := by
  have hdn' : (0 : ℝ) < dn := by exact_mod_cast hdn0
  have hd : (dn : ℝ) < D := by exact_mod_cast hdnD
  have hD0 : (0 : ℝ) < D := lt_trans hdn' hd
  have hδp0 : 0 < δ p := by rw [hδp]; positivity
  have hδp1 : δ p < 1 := by rw [hδp, div_lt_one hD0]; exact hd
  have hC' : 1 ≤ 4 * δ p * C := by
    rw [hδp]
    have := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ 4 * ((dn : ℝ) / D))
    have e : 4 * ((dn : ℝ) / D) * ((D : ℝ) / (4 * dn)) = 1 := by field_simp
    linarith
  refine (hingeLoss_le_moment_two_block hp hB hBp hδp0 hδp1 hδ hν Bq hBq hET hC' γ).trans
    (le_of_eq ?_)
  rw [hδp]
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hDd : (0 : ℝ) < (D : ℝ) - dn := by linarith
  field_simp

/-- **`blockVal`, θ = 3** (`k3`): with `C ≥ 4D²/(27 dn²)` (`cTheta3 dn = ratUp (4 DDEN²) (27 dn²)`),
`hingeLoss m δ p γ ≤ C · ET · D / ((B-1)³ (D - dn))`. -/
theorem hingeLoss_le_blockVal_three {m p B dn D : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hB : 2 ≤ B)
    (hBp : B ≤ p) (hδp : δ p = (dn : ℝ) / D) (hdn0 : 0 < dn) (hdnD : dn < D)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (Bq : ℕ → ℝ)
    (hBq : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 3) ≤ Bq q)
    {ET : ℝ} (hET : ∏ q ∈ Nat.primesBelow p, Bq q ≤ ET) {C : ℝ}
    (hC : 4 * (D : ℝ) ^ 2 / (27 * (dn : ℝ) ^ 2) ≤ C) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ C * ET * D / (((B : ℝ) - 1) ^ 3 * ((D : ℝ) - dn)) := by
  have hdn' : (0 : ℝ) < dn := by exact_mod_cast hdn0
  have hd : (dn : ℝ) < D := by exact_mod_cast hdnD
  have hD0 : (0 : ℝ) < D := lt_trans hdn' hd
  have hδp0 : 0 < δ p := by rw [hδp]; positivity
  have hδp1 : δ p < 1 := by rw [hδp, div_lt_one hD0]; exact hd
  have hC' : 4 ≤ 27 * δ p ^ 2 * C := by
    rw [hδp]
    have := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ 27 * ((dn : ℝ) / D) ^ 2)
    have e : 27 * ((dn : ℝ) / D) ^ 2 * (4 * (D : ℝ) ^ 2 / (27 * (dn : ℝ) ^ 2)) = 4 := by
      field_simp
    linarith
  refine (hingeLoss_le_moment_three_block hp hB hBp hδp0 hδp1 hδ hν Bq hBq hET hC' γ).trans
    (le_of_eq ?_)
  rw [hδp]
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hDd : (0 : ℝ) < (D : ℝ) - dn := by linarith
  field_simp

/-- **`blockVal`, θ = 5/2** (`k25 = cdiv (cTheta25 dn · ET25 · DDEN · 2^32) ((B-1)²·sq·(DDEN-dn)·ONE)`,
`sq = Nat.sqrt ((B-1)·2^64)`): with `a ≥ 6D/(25 dn)`, `b ≥ 0`, `b² ≥ 3D/(5 dn)`, `a·b ≤ C`
(`cTheta25 dn = mulUp (ratUp (6 DDEN) (25 dn)) (sqrtRatUp (3 DDEN) (5 dn))`) and
`0 < sq`, `sq² ≤ (B-1)·2^64`:
`hingeLoss m δ p γ ≤ C · ET · D · 2^32 / ((B-1)² · sq · (D - dn))`. -/
theorem hingeLoss_le_blockVal_five_halves {m p B dn D : ℕ} {δ : ℕ → ℝ} (hp : p.Prime)
    (hB : 2 ≤ B) (hBp : B ≤ p) (hδp : δ p = (dn : ℝ) / D) (hdn0 : 0 < dn) (hdnD : dn < D)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (Bq : ℕ → ℝ)
    (hBq : ∀ q ∈ Nat.primesBelow p, ∀ γ,
      expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤ Bq q)
    {ET : ℝ} (hET : ∏ q ∈ Nat.primesBelow p, Bq q ≤ ET) {a b C : ℝ}
    (ha : 6 * (D : ℝ) / (25 * dn) ≤ a) (hb0 : 0 ≤ b) (hb : 3 * (D : ℝ) / (5 * dn) ≤ b ^ 2)
    (hC : a * b ≤ C) {sq : ℕ} (hsq0 : 0 < sq) (hsq : sq * sq ≤ (B - 1) * 2 ^ 64)
    (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤
      C * ET * D * 2 ^ 32 / (((B : ℝ) - 1) ^ 2 * sq * ((D : ℝ) - dn)) := by
  have hdn' : (0 : ℝ) < dn := by exact_mod_cast hdn0
  have hd : (dn : ℝ) < D := by exact_mod_cast hdnD
  have hD0 : (0 : ℝ) < D := lt_trans hdn' hd
  have hδp0 : 0 < δ p := by rw [hδp]; positivity
  have hδp1 : δ p < 1 := by rw [hδp, div_lt_one hD0]; exact hd
  have hC' : ctheta (5 / 2) (δ p) ≤ C := by
    refine le_trans (ctheta_five_halves_le_mul hδp0 ?_ hb0 ?_) hC
    · rw [hδp]
      have e : 6 / (25 * ((dn : ℝ) / D)) = 6 * (D : ℝ) / (25 * dn) := by field_simp
      rw [e]
      exact ha
    · rw [hδp]
      have e : 3 / (5 * ((dn : ℝ) / D)) = 3 * (D : ℝ) / (5 * dn) := by field_simp
      rw [e]
      exact hb
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hsq' : (0 : ℝ) < sq := by exact_mod_cast hsq0
  have hr : ((sq : ℝ) / 2 ^ 32) ^ 2 ≤ (B : ℝ) - 1 := by
    have h1 : ((sq * sq : ℕ) : ℝ) ≤ (((B - 1) * 2 ^ 64 : ℕ) : ℝ) := by exact_mod_cast hsq
    push_cast [Nat.cast_sub (by omega : 1 ≤ B)] at h1
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  refine (hingeLoss_le_moment_five_halves_block hp hB hBp hδp0 hδp1 hδ hν Bq hBq hET hC'
    (by positivity : (0 : ℝ) < (sq : ℝ) / 2 ^ 32) hr γ).trans (le_of_eq ?_)
  rw [hδp]
  have hDd : (0 : ℝ) < (D : ℝ) - dn := by linarith
  field_simp

end MinModulus.CheckerMath
