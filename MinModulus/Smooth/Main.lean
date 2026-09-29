import MinModulus.Smooth.Law
import MinModulus.Smooth.Config
import MinModulus.Smooth.Tau
import MinModulus.Smooth.Weights
import MinModulus.Smooth.Hinge
import MinModulus.Smooth.Moments
import MinModulus.Smooth.Bounds

/-!
# Module 4 `Smooth`: the capped tilted smooth law and moment inequalities

## Status

COMPLETE.  No `sorry`, no `admit`, no new axioms.  `#print axioms` (see `Axioms.lean`) reports only
`propext`, `Classical.choice`, `Quot.sound` for every exported theorem.

Files (all in namespace `MinModulus.Smooth`):
* `Law.lean`     : `tailP`, `rho`, `expect1`; normalization, nonnegativity, tail/Abel formula,
                   one-coordinate coupling (`expect1_mono_cap`, `expect1_clip`), monotonicity in
                   the tilt (`expect1_mono_tilt`), `V`-law form (`rho_eq_min_sub`).
* `Config.lean`  : `box`, `weight`, `smooth`, `expect`; recursive decomposition `expect_insert`
                   (also `expect_insert'`, `expect_union_singleton`, `expect_singleton`),
                   (i) `sum_weight`/`expect_one`/`weight_nonneg`, (ii) `expect_mono_cap`/`expect_clip`,
                   `expect_le_of_forall_ge_cap`, tilt monotonicity `expect_mono_tilt`,
                   (iii) `expect_prod`, Fubini `expect_union`, marginalization, zero caps,
                   `expect_le_of_subset`, reindexing `sum_piFinset_eq_expect`/`sum_pi_fin_eq_expect`.
* `Tau.lean`     : `card_divisors_smooth`, `factorization_smooth`, `divisors_smooth`,
                   `smooth_dvd_smooth_iff`, `coprime_smooth_of_disjoint`,
                   (vii) `expect_tau_rpow`/`expect_tau_pow`.
* `Weights.lean` : `j0`, `wp`, `Up`; (vi) `wp_le`, `Up_le_card_div`; `sum_le_wp`, `hasSum_wp`,
                   `sum_pairs_le_Up` (enlargement), `Up_mono`, `monotone_Up_smooth`, `Up_mul_le`.
* `Hinge.lean`   : `ctheta`; (v) `hinge_le_ctheta_mul_rpow`, `hinge_le_sq_div`; `ctheta_two`,
                   `ctheta_three`, `ctheta_le_iff`, `ctheta_five_halves_le`; half-integer powers.
* `Moments.lean` : (iv) exact formulas, uniform bounds and limits for `θ = 2, 3`; the checker form
                   `expect1_rpow_le` for any real `θ ≥ 0`.
* `Bounds.lean`  : `expect1_five_halves_le` (rational certificate for `θ = 5/2`),
                   `expect1_five_halves_le_closed` (crude closed form), `monotone_hinge_Up`,
                   `expect_hinge_Up_le(_prod,_two)`, `expect_hinge_le_sq_div`,
                   `Up_smooth_union_le` (the `s_A s_B` split), `Up_smooth_eq`, `expect_Up_eq`.

## Changes relative to `LEAN_DESIGN.md` (all harmless; the mathematical content is unchanged)

* `rho q ν γ a` is defined through the tail `tailP q ν r` (`= 1` for `r = 0`, `ν q^{-r}` for `r ≥ 1`):
  `rho = tailP a - tailP (a+1)` for `a < γ`, `tailP γ` for `a = γ`, `0` for `a > γ`.  The explicit
  values of the design are the lemmas `rho_zero_zero`, `rho_zero_of_pos`, `rho_of_pos_of_lt`,
  `rho_self_of_pos`, `rho_of_gt`; `rho_eq_min_sub`/`rho_self_eq_min` give the comparison theorem's
  `min(1, ν q^{-r})` form.  `q^{-a}` is written `((q : ℝ)⁻¹) ^ a` throughout.
* Configurations are `v : ℕ → ℕ`, supported in `Ps`; `box Ps γ` is an explicit `Finset.map` of
  `Finset.pi` (no choice).  Tilts and caps are global functions `ν : ℕ → ℝ`, `γ : ℕ → ℕ`; only their
  values on `Ps` matter (`expect_congr_param`).
* Nonnegativity hypotheses are `∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q` (weaker than `1 ≤ ν ≤ q`); normalization,
  the recursive decomposition and the product formula need no hypotheses at all.
* Names: `s(v)` = `smooth Ps v`, `w_p(d)` = `wp p m d`, `U_p(s)` = `Up p m s`, `τ(n)` =
  `(n.divisors.card : ℝ)`, `c_θ(t)` = `ctheta θ t`, `E_γ[f]` = `expect Ps ν γ f`,
  one-coordinate expectation `expect1 q ν γ g`.
* `j0 p m d` is computable (`Nat.find`) and has the junk value `1` when `p ≤ 1` or `d = 0`.
* (iv) for `θ = 5/2`: the generic real-`θ` bound `expect1_rpow_le` plus the rational certificate
  `expect1_five_halves_le` (all side conditions are polynomial inequalities).
-/
