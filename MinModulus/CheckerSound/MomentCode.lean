import MinModulus.CheckerSound.Defs
import MinModulus.CheckerMath.ImplBridge

/-!
# CheckerSound (CS-A): scalar specifications used by the block phase

STATUS: complete, no `sorry`.

Most scalar specifications (`ratUp_ge`, `mulUp_ge`, `fac2_ge`, `fac3_ge`, `cTheta*_ge`,
`expect1_{sq,cube,five_halves}_le_fac*`, `tailFactor_le_fac2`, `hingeLoss_le_blockVal`) are in
`CheckerMath/ImplBridge.lean`; this file adds what the block loop needs on top of them:

* `pv_powUp` : `pv x ^ n ≤ pv (powUp x n)` (binary exponentiation rounds up);
* `pv_mulUp_le` : `a ≤ pv x → b ≤ pv y → a·b ≤ pv (mulUp x y)` (`a, b ≥ 0`);
* `facE1_ge`, `expect1_add_one_le_facE1` : `facE1 q dn / 2^62 ≥ 1 + ν/(q-1) ≥ E_γ[v+1]`;
* the per-prime moment factors `cubeFactor δ q = 1 + ν_q(7q²-2q+1)/(q-1)³` (θ = 3) and
  `fhFactor δ q = sup_γ E_γ[(v_q+1)^{5/2}]` (θ = 5/2), with `1 ≤ ·`, the expectation bounds, and
  their block bounds `cubeFactor_le_fac3`, `fhFactor_le_fac25` (any block start `2 ≤ Q ≤ q`);
* `tilt_delta0_eq` : the exact tilt of `delta0 P` in ImplBridge's form `D/(D - dn)`.
-/

namespace MinModulus.CheckerSound.A

open MinModulus.CheckerImpl MinModulus.Smooth MinModulus.CheckerMath MinModulus.Main
  MinModulus.CheckerSound Finset

/-! ### Constants and P-values -/

theorem DDEN_real' : ((DDEN : ℕ) : ℝ) = 10 ^ 9 := by norm_num [DDEN]

theorem DNMAX_lt_DDEN : DNMAX < DDEN := by decide

theorem pv_eq_div_ONE (x : ℕ) : pv x = (x : ℝ) / ONE := by rw [ONE_real]; rfl

/-- Truncated subtraction is `≥` the real difference. -/
theorem natsub_real (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

/-- `mulUp` rounds up, in the form used for running products. -/
theorem pv_mulUp_le {x y : ℕ} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ pv x)
    (hb : b ≤ pv y) : a * b ≤ pv (mulUp x y) :=
  (mul_le_mul ha hb hb0 (ha0.trans ha)).trans (pv_mul_le_mulUp x y)

theorem powUpAux_ge (b e acc : ℕ) : pv acc * pv b ^ e ≤ pv (powUpAux b e acc) := by
  induction e using Nat.strong_induction_on generalizing b acc with
  | _ e ih =>
    rw [powUpAux]
    by_cases h0 : e = 0
    · subst h0; simp
    · simp only [h0, ↓reduceDIte]
      have hlt : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by norm_num)
      have hb2 : pv b ^ 2 ≤ pv (mulUp b b) := by rw [sq]; exact pv_mul_le_mulUp b b
      have hpow : (pv b ^ 2) ^ (e / 2) ≤ pv (mulUp b b) ^ (e / 2) :=
        pow_le_pow_left₀ (by positivity) hb2 _
      have hx0 : 0 ≤ pv b := pv_nonneg b
      have hy0 : 0 ≤ pv acc := pv_nonneg acc
      by_cases h1 : e % 2 = 1
      · simp only [h1, ↓reduceIte]
        refine le_trans ?_ (ih (e / 2) hlt (mulUp b b) (mulUp acc b))
        have he : e = 2 * (e / 2) + 1 := by omega
        have key : pv acc * pv b ^ e = (pv acc * pv b) * (pv b ^ 2) ^ (e / 2) := by
          generalize e / 2 = k at he ⊢
          subst he
          ring
        rw [key]
        exact mul_le_mul (pv_mul_le_mulUp acc b) hpow (by positivity) (pv_nonneg _)
      · simp only [h1, ↓reduceIte]
        refine le_trans ?_ (ih (e / 2) hlt (mulUp b b) acc)
        have he : e = 2 * (e / 2) := by omega
        have key : pv acc * pv b ^ e = pv acc * (pv b ^ 2) ^ (e / 2) := by
          generalize e / 2 = k at he ⊢
          subst he
          ring
        rw [key]
        exact mul_le_mul_of_nonneg_left hpow hy0

/-- **`powUp` rounds up**: `(x/2^62)^n ≤ powUp x n / 2^62`. -/
theorem pv_powUp (x n : ℕ) : pv x ^ n ≤ pv (powUp x n) := by
  have h := powUpAux_ge x n ONE
  rwa [pv_ONE, one_mul] at h

/-! ### The tilt of `delta0` -/

/-- `tilt (delta0 P) q = D/(D - dn)` with `D = 10^9`, `dn = deltaN P q` (for `q ≤ X`), in the
form of ImplBridge's hypotheses. -/
theorem tilt_delta0_eq {P : Params} {q : ℕ} (h : q ≤ P.PMAX) :
    tilt (delta0 P) q = (DDEN : ℝ) / ((DDEN : ℝ) - deltaN P q) := by
  rw [tilt_delta0_of_le h, DDEN_real']

theorem deltaN_lt_DDEN (P : Params) (q : ℕ) : deltaN P q < DDEN :=
  lt_of_le_of_lt (deltaN_le P q) (by decide)

/-- `D/(D - dn) ≤ 2` for `dn ≤ 0.45·D`. -/
theorem nu_le_two {dn : ℕ} (h : dn ≤ 450000000) : (DDEN : ℝ) / ((DDEN : ℝ) - dn) ≤ 2 := by
  rw [DDEN_real']
  have h' : (dn : ℝ) ≤ 450000000 := by exact_mod_cast h
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem nu_nonneg {dn : ℕ} (h : dn < DDEN) : 0 ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn) := by
  have : (dn : ℝ) < DDEN := by exact_mod_cast h
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

/-! ### `facE1` (used by the τ-DPs) -/

/-- `facE1 q dn / 2^62 ≥ 1 + ν/(q-1)`, `ν = D/(D - dn)`. -/
theorem facE1_ge {q dn : ℕ} (hq : 2 ≤ q) (hdn : dn < DDEN) :
    1 + (DDEN : ℝ) / ((DDEN : ℝ) - dn) / ((q : ℝ) - 1) ≤ pv (facE1 q dn) := by
  rw [pv_eq_div_ONE]
  unfold facE1 nuDen
  have hd0 : 0 < (q - 1) * (DDEN - dn) := Nat.mul_pos (by omega) (by omega)
  refine le_trans (le_of_eq ?_) (ratUp_ge hd0)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hd : (dn : ℝ) < DDEN := by exact_mod_cast hdn
  push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hdn.le]
  have : (q : ℝ) - 1 ≠ 0 := by linarith
  have : (DDEN : ℝ) - dn ≠ 0 := by linarith
  field_simp

/-- `E_{q,ν,γ}[v + 1] ≤ facE1 q dn / 2^62` for `0 ≤ ν ≤ D/(D - dn)`, every cap. -/
theorem expect1_add_one_le_facE1 {q dn : ℕ} (hq : 2 ≤ q) (hdn : dn < DDEN) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn)) (γ : ℕ) :
    expect1 q ν γ (fun a => (a : ℝ) + 1) ≤ pv (facE1 q dn) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have h1 : expect1 q ν γ (fun a => (a : ℝ) + 1) = ∑ a ∈ range (γ + 1), tailP q ν a := by
    rw [expect1_eq_tail, sum_range_succ', tailP_zero]
    simp only [Nat.cast_add, Nat.cast_one]
    ring_nf
  rw [h1]
  refine (sum_tailP_le (by omega) hν0 γ).trans ?_
  refine le_trans ?_ (facE1_ge hq hdn)
  have : ν / ((q : ℝ) - 1) ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn) / ((q : ℝ) - 1) :=
    div_le_div_of_nonneg_right hν (by linarith)
  linarith

/-! ### The per-prime moment factors of the running products -/

/-- The θ = 3 factor `1 + ν_q (7q² - 2q + 1)/(q - 1)³` (`≥ E_γ[(v_q+1)³]` for every cap). -/
noncomputable def cubeFactor (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  1 + tilt δ q * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3

/-- The θ = 5/2 factor: the supremum over the caps of `E_γ[(v_q+1)^{5/2}]`. -/
noncomputable def fhFactor (δ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ⨆ γ : ℕ, expect1 q (tilt δ q) γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ))

theorem one_le_cubeFactor {δ : ℕ → ℝ} {q : ℕ} (hq : 1 ≤ q) (h0 : 0 ≤ tilt δ q) :
    1 ≤ cubeFactor δ q := by
  unfold cubeFactor
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have : 0 ≤ tilt δ q * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 :=
    div_nonneg (mul_nonneg h0 (by nlinarith)) (pow_nonneg (by linarith) 3)
  linarith

theorem expect1_cube_le_cubeFactor {δ : ℕ → ℝ} {q : ℕ} (hq : 1 < q) (h0 : 0 ≤ tilt δ q)
    (γ : ℕ) : expect1 q (tilt δ q) γ (fun a => ((a : ℝ) + 1) ^ 3) ≤ cubeFactor δ q :=
  expect1_cube_le hq h0 γ

theorem expect1_sq_le_tailFactor {δ : ℕ → ℝ} {q : ℕ} (hq : 1 < q) (h0 : 0 ≤ tilt δ q)
    (γ : ℕ) : expect1 q (tilt δ q) γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ tailFactor δ q :=
  expect1_sq_le hq h0 γ

theorem fhFactor_bdd {δ : ℕ → ℝ} {q : ℕ} (hq : 1 < q) (h0 : 0 ≤ tilt δ q)
    (hq' : tilt δ q ≤ q) :
    BddAbove (Set.range fun γ : ℕ =>
      expect1 q (tilt δ q) γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ))) :=
  ⟨_, Set.forall_mem_range.2 fun γ => expect1_five_halves_le_closed hq h0 hq' γ⟩

theorem expect1_le_fhFactor {δ : ℕ → ℝ} {q : ℕ} (hq : 1 < q) (h0 : 0 ≤ tilt δ q)
    (hq' : tilt δ q ≤ q) (γ : ℕ) :
    expect1 q (tilt δ q) γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤ fhFactor δ q :=
  le_ciSup (fhFactor_bdd hq h0 hq') γ

theorem one_le_fhFactor {δ : ℕ → ℝ} {q : ℕ} (hq : 1 < q) (h0 : 0 ≤ tilt δ q)
    (hq' : tilt δ q ≤ q) : 1 ≤ fhFactor δ q := by
  refine le_trans (le_of_eq ?_) (expect1_le_fhFactor hq h0 hq' 0)
  simp

/-- Block form of `cubeFactor ≤ fac3`: `2 ≤ Q ≤ q`, `tilt δ q ≤ D/(D - dn)`. -/
theorem cubeFactor_le_fac3 {δ : ℕ → ℝ} {q Q dn : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q)
    (hdn : dn < DDEN) (h0 : 0 ≤ tilt δ q) (hν : tilt δ q ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn)) :
    cubeFactor δ q ≤ pv (fac3 Q dn) := by
  rw [pv_eq_div_ONE]
  refine le_trans ?_ (fac3_ge hQ hdn)
  unfold cubeFactor
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hQ.trans hQq
  have hf0 : 0 ≤ (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 :=
    div_nonneg (by nlinarith) (pow_nonneg (by linarith) 3)
  have h1 : tilt δ q * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 ≤
      (DDEN : ℝ) / ((DDEN : ℝ) - dn) * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hν hf0
  have h2 : (DDEN : ℝ) / ((DDEN : ℝ) - dn) * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 ≤
      (DDEN : ℝ) / ((DDEN : ℝ) - dn) * (7 * (Q : ℝ) ^ 2 - 2 * Q + 1) / ((Q : ℝ) - 1) ^ 3 := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (cubeFactor_anti hQ hQq) (h0.trans hν)
  linarith

/-- Block form of `fhFactor ≤ fac25`: `2 ≤ Q ≤ q`, `tilt δ q ≤ D/(D - dn)`, `dn ≤ 0.45·D`. -/
theorem fhFactor_le_fac25 {δ : ℕ → ℝ} {q Q dn : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q)
    (hdn : dn ≤ 450000000) (h0 : 0 ≤ tilt δ q)
    (hν : tilt δ q ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn)) :
    fhFactor δ q ≤ pv (fac25 Q dn) := by
  rw [pv_eq_div_ONE]
  have hdn' : dn < DDEN := lt_of_le_of_lt hdn (by decide)
  have hDQ : (DDEN : ℝ) / ((DDEN : ℝ) - dn) ≤ Q :=
    (nu_le_two hdn).trans (by exact_mod_cast hQ)
  exact ciSup_le fun γ => expect1_five_halves_le_fac25 hQ hQq hdn' hDQ h0 hν γ

end MinModulus.CheckerSound.A
