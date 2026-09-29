import MinModulus.CheckerSound.TauDPArray
import MinModulus.CheckerMath.GFun
import Mathlib.Algebra.BigOperators.Field

/-!
# `CheckerSound.TauDPReal` (agent CS-B): real-number specifications of the τ-DP building blocks

Status: complete, no `sorry`.

P-values: a natural `x` stands for the real `x / 2^62`; statements are written with
`(x : ℝ) / 2 ^ 62` literally. δ-values: `dn` stands for `δ = dn / 10^9`; the exact tilt is
`tiltN dn = 1 / (1 - dn/10^9) = 10^9/(10^9 - dn)` (`tiltN_eq`), i.e. `Main.tilt δ₀ q` for
`δ₀ q = dn_q / 10^9`.

* rounding: `ratUp_ge_real`, `ratDn_le_real`, `mulUp_ge_real`, `mulDn_le_real`, `cdiv_ge_real`, `sub_le_cast_tsub`;
* tilts: `tiltN`, `tiltN_eq`, `tiltN_mem` (`0 ≤ ν ≤ q` for `q ≥ 2`, `δ ≤ 1/2`);
* **`mkExpLaw`** (item 1): `mkExpLaw_rho_le_up`, `mkExpLaw_dn_le_rho` (for every cap `γ > a`),
  `mkExpLaw_lostUp_ge`; the point masses `pmass`, `pmass_le_expUpE`, `expDnE_le_pmass`;
* `facE1_ge`: `1 + ν/(q-1) ≤ facE1/2^62`; `meanTau_insert`, `meanTau_insert_le`;
* **`dpStep`** (item 2, one step): `lawKept_insert_le_dpStep` (upper, `mulUp`),
  `dpStep_le_lawKept_insert` (lower, `mulDn`); the initial array `lawKept_empty_eq_init`.
-/

namespace MinModulus.CheckerSound.B

open MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Smooth Finset

/-! ### Rounding primitives in `ℝ` -/

theorem two_pow_62_pos : (0 : ℝ) < 2 ^ 62 := by positivity

theorem cast_ONE : ((ONE : ℕ) : ℝ) = 2 ^ 62 := by
  rw [ONE_eq]
  push_cast
  ring

theorem cast_DDEN : ((DDEN : ℕ) : ℝ) = 10 ^ 9 := by
  rw [show DDEN = 10 ^ 9 from rfl]
  push_cast
  ring

theorem ratUp_ge_real {num den : ℕ} (h : 0 < den) :
    (num : ℝ) / den ≤ (ratUp num den : ℝ) / 2 ^ 62 := by
  have h1 := ratUp_spec (num := num) h
  have h2 : (num : ℝ) * 2 ^ 62 ≤ (ratUp num den : ℝ) * den := by
    rw [← cast_ONE]
    exact_mod_cast h1
  have hd : (0 : ℝ) < den := by exact_mod_cast h
  rw [div_le_div_iff₀ hd two_pow_62_pos]
  exact h2

theorem ratDn_le_real {num den : ℕ} (h : 0 < den) :
    (ratDn num den : ℝ) / 2 ^ 62 ≤ (num : ℝ) / den := by
  have h1 := ratDn_spec num den
  have h2 : (ratDn num den : ℝ) * den ≤ (num : ℝ) * 2 ^ 62 := by
    rw [← cast_ONE]
    exact_mod_cast h1
  have hd : (0 : ℝ) < den := by exact_mod_cast h
  rw [div_le_div_iff₀ two_pow_62_pos hd]
  exact h2

theorem mulUp_ge_real (x y : ℕ) :
    (x : ℝ) / 2 ^ 62 * ((y : ℝ) / 2 ^ 62) ≤ (mulUp x y : ℝ) / 2 ^ 62 := by
  have h1 := mulUp_spec x y
  have h2 : (x : ℝ) * y ≤ (mulUp x y : ℝ) * 2 ^ 62 := by
    rw [← cast_ONE]
    exact_mod_cast h1
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) two_pow_62_pos]
  nlinarith [two_pow_62_pos]

theorem mulDn_le_real (x y : ℕ) :
    (mulDn x y : ℝ) / 2 ^ 62 ≤ (x : ℝ) / 2 ^ 62 * ((y : ℝ) / 2 ^ 62) := by
  have h1 := mulDn_spec x y
  have h2 : (mulDn x y : ℝ) * 2 ^ 62 ≤ (x : ℝ) * y := by
    rw [← cast_ONE]
    exact_mod_cast h1
  rw [div_mul_div_comm, div_le_div_iff₀ two_pow_62_pos (by positivity)]
  nlinarith [two_pow_62_pos]

theorem cdiv_ge_real {a b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  have h1 := cdiv_spec (a := a) hb
  have h2 : (a : ℝ) ≤ (cdiv a b : ℝ) * b := by exact_mod_cast h1
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  exact h2

/-- Truncated subtraction bounds the real difference from above. -/
theorem sub_le_cast_tsub (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

theorem mulR_true (x y : ℕ) : mulR true x y = mulUp x y := by simp [mulR]

theorem mulR_false (x y : ℕ) : mulR false x y = mulDn x y := by simp [mulR]

/-! ### Exact tilts -/

/-- The exact tilt of the checker for the δ-value `dn` (`δ = dn/10^9`):
`ν = 1/(1 - dn/10^9)` (this is `Main.tilt δ₀ q` for `δ₀ q = dn/10^9`). -/
noncomputable def tiltN (dn : ℕ) : ℝ := 1 / (1 - (dn : ℝ) / 10 ^ 9)

theorem tiltN_eq {dn : ℕ} (h : dn < DDEN) : tiltN dn = 10 ^ 9 / ((10 : ℝ) ^ 9 - dn) := by
  have h' : (dn : ℝ) < 10 ^ 9 := by rw [← cast_DDEN]; exact_mod_cast h
  have h2 : (10 : ℝ) ^ 9 - dn ≠ 0 := by linarith
  unfold tiltN
  field_simp

theorem cast_nuDen {dn : ℕ} (h : dn ≤ DDEN) : ((nuDen dn : ℕ) : ℝ) = 10 ^ 9 - dn := by
  unfold nuDen
  rw [Nat.cast_sub h, cast_DDEN]

theorem nuDen_pos {dn : ℕ} (h : dn < DDEN) : 0 < nuDen dn := by
  unfold nuDen
  omega

/-- `ν = 10^9 / nd` with `nd = nuDen dn = 10^9 - dn`. -/
theorem tiltN_eq_div_nuDen {dn : ℕ} (h : dn < DDEN) :
    tiltN dn = 10 ^ 9 / ((nuDen dn : ℕ) : ℝ) := by
  rw [tiltN_eq h, cast_nuDen h.le]

theorem one_le_tiltN (dn : ℕ) (h : 2 * dn ≤ DDEN) : 1 ≤ tiltN dn := by
  have h' : (dn : ℝ) ≤ 10 ^ 9 / 2 := by
    have : ((2 * dn : ℕ) : ℝ) ≤ ((DDEN : ℕ) : ℝ) := by exact_mod_cast h
    rw [cast_DDEN] at this
    push_cast at this
    linarith
  have hd0 : (0 : ℝ) ≤ dn := Nat.cast_nonneg dn
  unfold tiltN
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem tiltN_le_two (dn : ℕ) (h : 2 * dn ≤ DDEN) : tiltN dn ≤ 2 := by
  have h' : (dn : ℝ) ≤ 10 ^ 9 / 2 := by
    have : ((2 * dn : ℕ) : ℝ) ≤ ((DDEN : ℕ) : ℝ) := by exact_mod_cast h
    rw [cast_DDEN] at this
    push_cast at this
    linarith
  unfold tiltN
  rw [div_le_iff₀ (by linarith)]
  linarith

/-- The exact tilts satisfy `Smooth`'s standing hypothesis `0 ≤ ν ≤ q` (`q ≥ 2`, `δ ≤ 1/2`). -/
theorem tiltN_mem {q : ℕ} (hq : 2 ≤ q) {dn : ℕ} (h : 2 * dn ≤ DDEN) :
    0 ≤ tiltN dn ∧ tiltN dn ≤ q := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  exact ⟨zero_le_one.trans (one_le_tiltN dn h), (tiltN_le_two dn h).trans hq'⟩

/-! ### Point masses and `mkExpLaw` (item 1) -/

/-- The untruncated point mass `P(V = a)` of the tilted exponent law (`= ρ(q, ν, γ, a)` for
`a < γ`, `CheckerMath.rho_eq_pointMass`). -/
noncomputable def pmass (q : ℕ) (ν : ℝ) (a : ℕ) : ℝ :=
  if a = 0 then 1 - ν / q else ν * ((q : ℝ)⁻¹) ^ a * (1 - (q : ℝ)⁻¹)

theorem rho_eq_pmass {q : ℕ} {ν : ℝ} {γ a : ℕ} (h : a < γ) : rho q ν γ a = pmass q ν a :=
  rho_eq_pointMass h

/-- Nat facts for the entries of the law: `q·nd ≥ 10^9` (`ν ≤ q`). -/
theorem DDEN_le_q_mul_nuDen {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) :
    DDEN ≤ q * nuDen dn := by
  unfold nuDen
  have : 2 * (DDEN - dn) ≤ q * (DDEN - dn) := Nat.mul_le_mul_right _ hq
  omega

theorem pmass_zero_eq {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) :
    pmass q (tiltN dn) 0 = (((q * nuDen dn - DDEN : ℕ) : ℝ)) / ((q * nuDen dn : ℕ) : ℝ) := by
  have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
  have hle := DDEN_le_q_mul_nuDen hq h
  have hnd := nuDen_pos hlt
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hnd0 : (0 : ℝ) < ((nuDen dn : ℕ) : ℝ) := by exact_mod_cast hnd
  unfold pmass
  rw [ite_eq_left rfl, tiltN_eq_div_nuDen hlt, Nat.cast_sub hle, cast_DDEN]
  push_cast
  field_simp

theorem pmass_pos_eq {q dn a : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) (ha : a ≠ 0) :
    pmass q (tiltN dn) a =
      (((DDEN * (q - 1) : ℕ) : ℝ)) / ((nuDen dn * q ^ (a + 1) : ℕ) : ℝ) := by
  have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
  have hnd := nuDen_pos hlt
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hnd0 : (0 : ℝ) < ((nuDen dn : ℕ) : ℝ) := by exact_mod_cast hnd
  unfold pmass
  rw [ite_eq_right ha, tiltN_eq_div_nuDen hlt]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ q), cast_DDEN]
  push_cast
  simp only [inv_pow]
  field_simp
  ring

theorem pmass_le_expUpE {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) (a : ℕ) :
    pmass q (tiltN dn) a ≤ (expUpE q (nuDen dn) a : ℝ) / 2 ^ 62 := by
  have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
  have hnd := nuDen_pos hlt
  unfold expUpE
  split_ifs with ha
  · subst ha
    rw [pmass_zero_eq hq h]
    exact ratUp_ge_real (Nat.mul_pos (by omega) hnd)
  · rw [pmass_pos_eq hq h ha]
    exact ratUp_ge_real (Nat.mul_pos hnd (pow_pos (by omega : 0 < q) _))

theorem expDnE_le_pmass {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) (a : ℕ) :
    (expDnE q (nuDen dn) a : ℝ) / 2 ^ 62 ≤ pmass q (tiltN dn) a := by
  have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
  have hnd := nuDen_pos hlt
  unfold expDnE
  split_ifs with ha
  · subst ha
    rw [pmass_zero_eq hq h]
    exact ratDn_le_real (Nat.mul_pos (by omega) hnd)
  · rw [pmass_pos_eq hq h ha]
    exact ratDn_le_real (Nat.mul_pos hnd (pow_pos (by omega : 0 < q) _))

/-- **`mkExpLaw`, upper entries** (every cap `γ > a`): `ρ(q, ν, γ, a) ≤ up[a]/2^62` for
`a ≤ acut`. -/
theorem mkExpLaw_rho_le_up {q dn bits : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) {γ a : ℕ}
    (ha : a ≤ (mkExpLaw q dn bits).acut) (haγ : a < γ) :
    rho q (tiltN dn) γ a ≤ ((mkExpLaw q dn bits).up[a]! : ℝ) / 2 ^ 62 := by
  rw [rho_eq_pmass haγ, mkExpLaw_up q dn bits ha]
  exact pmass_le_expUpE hq h a

/-- **`mkExpLaw`, lower entries** (every cap `γ > a`): `dn[a]/2^62 ≤ ρ(q, ν, γ, a)` for
`a ≤ acut`. -/
theorem mkExpLaw_dn_le_rho {q dn bits : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) {γ a : ℕ}
    (ha : a ≤ (mkExpLaw q dn bits).acut) (haγ : a < γ) :
    ((mkExpLaw q dn bits).dn[a]! : ℝ) / 2 ^ 62 ≤ rho q (tiltN dn) γ a := by
  rw [rho_eq_pmass haγ, mkExpLaw_dn q dn bits ha]
  exact expDnE_le_pmass hq h a

/-- **`mkExpLaw`, lost exponent mass**: `ν q^{-(acut+1)} ≤ lostUp/2^62`. -/
theorem mkExpLaw_lostUp_ge {q dn bits : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) :
    tiltN dn * ((q : ℝ)⁻¹) ^ ((mkExpLaw q dn bits).acut + 1) ≤
      ((mkExpLaw q dn bits).lostUp : ℝ) / 2 ^ 62 := by
  have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
  have hnd := nuDen_pos hlt
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hnd0 : (0 : ℝ) < ((nuDen dn : ℕ) : ℝ) := by exact_mod_cast hnd
  rw [mkExpLaw_lostUp]
  refine le_of_eq_of_le ?_ (ratUp_ge_real (Nat.mul_pos hnd (pow_pos (by omega : 0 < q) _)))
  rw [tiltN_eq_div_nuDen hlt, cast_DDEN]
  push_cast
  simp only [inv_pow]
  field_simp

/-! ### `E[v + 1]` factors: `facE1` and `meanTau` -/

theorem facE1_ge {q dn : ℕ} (hq : 2 ≤ q) (h : dn < DDEN) :
    1 + tiltN dn / ((q : ℝ) - 1) ≤ (facE1 q dn : ℝ) / 2 ^ 62 := by
  have hnd := nuDen_pos h
  have hq1 : 0 < q - 1 := by omega
  have hq0 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hnd0 : (0 : ℝ) < ((nuDen dn : ℕ) : ℝ) := by exact_mod_cast hnd
  unfold facE1
  refine le_of_eq_of_le ?_ (ratUp_ge_real (Nat.mul_pos hq1 hnd))
  rw [tiltN_eq_div_nuDen h]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ q), cast_DDEN]
  push_cast
  field_simp

theorem meanTau_insert {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) :
    meanTau (insert q Ps) ν γ =
      expect1 q (ν q) (γ q) (fun a => (a : ℝ) + 1) * meanTau Ps ν γ := by
  unfold meanTau
  simp_rw [tauN_cast]
  rw [expect_prod (insert q Ps) ν γ (fun _ a => (a : ℝ) + 1),
    expect_prod Ps ν γ (fun _ a => (a : ℝ) + 1), prod_insert hq]

theorem meanTau_insert_le {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) (hq2 : 2 ≤ q) {ν : ℕ → ℝ}
    (hν : ∀ r ∈ insert q Ps, 0 ≤ ν r ∧ ν r ≤ r) (γ : ℕ → ℕ) {E F : ℝ}
    (hE : meanTau Ps ν γ ≤ E) (hF : 1 + ν q / ((q : ℝ) - 1) ≤ F) :
    meanTau (insert q Ps) ν γ ≤ E * F := by
  rw [meanTau_insert hq]
  have hνq := hν q (mem_insert_self q Ps)
  have hν' : ∀ r ∈ Ps, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
  have h1 := expect1_add_one_le (by omega : 1 < q) hνq.1 (γ q)
  have h0 : 0 ≤ expect1 q (ν q) (γ q) (fun a => (a : ℝ) + 1) :=
    expect1_nonneg hνq.1 hνq.2 fun a _ => by positivity
  have hM0 := meanTau_nonneg hν' γ
  rw [mul_comm E F]
  exact mul_le_mul (h1.trans hF) hE hM0 (h0.trans (h1.trans hF))

/-! ### The DP step in `ℝ` (item 2) -/

theorem cast_dpStep_get (up : Bool) (D : Array ℕ) (N : ℕ) (law : Array ℕ) (acut : ℕ) {T : ℕ}
    (hT : T < N) :
    ((dpStep up D N law acut)[T]! : ℝ) / 2 ^ 62 =
      ∑ t ∈ Ico 1 N, ∑ a ∈ range (acut + 1),
        if t * (a + 1) = T then (mulR up D[t]! law[a]! : ℝ) / 2 ^ 62 else 0 := by
  rw [dpStep_get up D N law acut hT]
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

/-- Dropping the `t = 0` column of the push-form sum (it only hits `T = 0`). -/
theorem sum_range_eq_sum_Ico_one {N T : ℕ} (hN : 0 < N) (hT : T ≠ 0) (acut : ℕ)
    (F : ℕ → ℕ → ℝ) :
    ∑ t ∈ range N, ∑ a ∈ range (acut + 1), (if t * (a + 1) = T then F t a else 0) =
      ∑ t ∈ Ico 1 N, ∑ a ∈ range (acut + 1), (if t * (a + 1) = T then F t a else 0) := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hN]
  have : ∑ a ∈ range (acut + 1), (if 0 * (a + 1) = T then F 0 a else 0) = 0 :=
    sum_eq_zero fun a _ => by rw [ite_eq_right (by omega)]
  rw [this, zero_add]

/-- **One upper DP step** (`dpStep true`, i.e. `mulUp`): if `D ≥ P_old(τ = ·, kept)` on
`[0, N)` and `law ≥ ρ_q` on `[0, acut q]`, then `dpStep true D N law (acut q) ≥ P_new(τ = ·,
kept)` on `[0, N)` (`TM = N - 1`). -/
theorem lawKept_insert_le_dpStep {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) {ν : ℕ → ℝ}
    (hν : ∀ r ∈ insert q Ps, 0 ≤ ν r ∧ ν r ≤ r) (γ : ℕ → ℕ) (acut : ℕ → ℕ) (D : Array ℕ)
    {N : ℕ} (law : Array ℕ)
    (hD : ∀ t < N, lawKept Ps ν γ (N - 1) acut t ≤ (D[t]! : ℝ) / 2 ^ 62)
    (hℓ : ∀ a ≤ acut q, rho q (ν q) (γ q) a ≤ (law[a]! : ℝ) / 2 ^ 62) {T : ℕ} (hT : T < N) :
    lawKept (insert q Ps) ν γ (N - 1) acut T ≤
      ((dpStep true D N law (acut q))[T]! : ℝ) / 2 ^ 62 := by
  rcases Nat.eq_zero_or_pos T with rfl | hT0
  · rw [lawKept_zero]
    positivity
  have h := lawKept_insert_le hq hν γ (N - 1) acut (fun t => (D[t]! : ℝ) / 2 ^ 62)
    (fun a => (law[a]! : ℝ) / 2 ^ 62) (fun t ht => hD t (by omega)) hℓ (T := T) (by omega)
  rw [show N - 1 + 1 = N by omega, sum_range_eq_sum_Ico_one (by omega) (by omega)] at h
  refine h.trans ?_
  rw [cast_dpStep_get true D N law (acut q) hT]
  refine sum_le_sum fun t _ => sum_le_sum fun a _ => ?_
  split_ifs
  · rw [mulR_true]
    exact mulUp_ge_real _ _
  · exact le_rfl

/-- **One lower DP step** (`dpStep false`, i.e. `mulDn`): if `D ≤ P_old(τ = ·, kept)` on
`[0, N)` and `law ≤ ρ_q` on `[0, acut q]`, then `dpStep false D N law (acut q) ≤ P_new(τ = ·,
kept)` on `[0, N)`. -/
theorem dpStep_le_lawKept_insert {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) {ν : ℕ → ℝ}
    (γ : ℕ → ℕ) (acut : ℕ → ℕ) (D : Array ℕ) {N : ℕ} (law : Array ℕ)
    (hD : ∀ t < N, (D[t]! : ℝ) / 2 ^ 62 ≤ lawKept Ps ν γ (N - 1) acut t)
    (hℓ : ∀ a ≤ acut q, (law[a]! : ℝ) / 2 ^ 62 ≤ rho q (ν q) (γ q) a) {T : ℕ} (hT : T < N) :
    ((dpStep false D N law (acut q))[T]! : ℝ) / 2 ^ 62 ≤
      lawKept (insert q Ps) ν γ (N - 1) acut T := by
  rw [cast_dpStep_get false D N law (acut q) hT]
  rcases Nat.eq_zero_or_pos T with rfl | hT0
  · rw [lawKept_zero]
    refine le_of_eq (sum_eq_zero fun t ht => sum_eq_zero fun a _ => ?_)
    have : 1 ≤ t := (mem_Ico.1 ht).1
    rw [ite_eq_right (by positivity)]
  have h := le_lawKept_insert hq γ (N - 1) acut (fun t => (D[t]! : ℝ) / 2 ^ 62)
    (fun a => (law[a]! : ℝ) / 2 ^ 62) (fun t _ => by positivity) (fun t ht => hD t (by omega))
    (fun a _ => by positivity) hℓ (T := T) (by omega)
  rw [show N - 1 + 1 = N by omega, sum_range_eq_sum_Ico_one (by omega) (by omega)] at h
  refine le_trans ?_ h
  refine sum_le_sum fun t _ => sum_le_sum fun a _ => ?_
  split_ifs
  · rw [mulR_false]
    exact mulDn_le_real _ _
  · exact le_rfl

/-- The initial DP array `(replicate N 0).set! 1 ONE` is exactly the law of `τ` on the empty set
of primes (`τ = 1`). -/
theorem lawKept_empty_eq_init (ν : ℕ → ℝ) (γ : ℕ → ℕ) {N : ℕ} (hN : 2 ≤ N) (acut : ℕ → ℕ)
    (T : ℕ) :
    lawKept ∅ ν γ (N - 1) acut T = (((Array.replicate N 0).set! 1 ONE)[T]! : ℝ) / 2 ^ 62 := by
  rw [lawKept_empty ν γ (by omega) acut T, getElem!_init N T (by omega)]
  split_ifs
  · rw [cast_ONE, div_self (by positivity)]
  · simp

end MinModulus.CheckerSound.B
