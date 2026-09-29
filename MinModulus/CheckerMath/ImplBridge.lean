import MinModulus.CheckerMath.Glue
import MinModulus.CheckerImpl.Moments
import Mathlib.Algebra.BigOperators.Field

/-!
# CheckerMath: bridge to the landed `CheckerImpl` (moment range and first moment)

STATUS: complete, no `sorry`. Owned by the CheckerMath (first moment / moments / glue) agent.
This is the only CheckerMath file that imports `CheckerImpl` (the executable checker); the other
CheckerMath files are independent of it.

It proves that the checker's numbers for the primes handled by the first moment and by the
moment bounds are upper bounds of the corresponding real quantities (P-values: `x / 2^62`,
`ONE = 2^62`; δ-values `dn / 10^9`, `DDEN = 10^9`; exact tilts `ν = 10^9/(10^9 - dn)`).

* Rounding in real terms: `ratUp_ge`, `cdiv_ge`, `mulUp_ge`, `le_sqrtUp_sq`, `sqrtUp_le_of_le_sq`.
* Factors: `fac2_ge`, `fac3_ge` (closed forms), and, uniform in the cap and valid for every prime
  `q ≥ Q` of a block starting at `Q`: `expect1_sq_le_fac2`, `expect1_cube_le_fac3`,
  `expect1_five_halves_le_fac25` (via the loop bound `fac25Sub_le`), and `tailFactor_le_fac2`.
* Constants: `cTheta2_ge`, `cTheta3_ge`, `cTheta25_ge`.
* **`hingeLoss_le_blockVal`**: `hingeLoss m δ p γ ≤ blockVal B dn ET2 ET25 ET3 / 2^62` for a prime
  `p` of the block `[B, …)`, given `Π_{q<p} B_θ(q) ≤ ET_θ/2^62` (θ = 2, 5/2, 3).
* **`hingeLoss_le_firstMoment_impl`**: `hingeLoss m δ p γ ≤ firstMoment m p ps / 2^62` when
  `δ_q = 0` for `q ≤ p` and `ps` lists the primes below `p` without duplicates
  (soundness of `isSmoothOver`, `numThresholdsAbove`, and of the loop `firstMoment.go`).

What remains for the certificate (`CheckerSound`): the loop invariants of `run` (the `ET_θ`
products, `etaA + etaB = Σ costs`, the block partition and `count ≥ #primes` from the sieve,
`costOf`), the comparison bound for `31 ≤ p ≤ PX` (other CheckerMath files), and assembling
`Glue.cert_of_check` with `CheckerImpl.checkWith_spec`.
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth MinModulus.Main MinModulus.CheckerImpl

/-! ### Rounding primitives, in real terms -/

theorem ONE_pos : 0 < ONE := by decide

theorem ONE_real : (ONE : ℝ) = 2 ^ 62 := by rw [ONE_eq]; norm_num

theorem DDEN_pos : 0 < DDEN := by decide

theorem ratUp_ge {num den : ℕ} (h : 0 < den) : (num : ℝ) / den ≤ (ratUp num den : ℝ) / ONE := by
  have h1 := ratUp_spec (num := num) h
  have h2 : (num : ℝ) * ONE ≤ (ratUp num den : ℝ) * den := by exact_mod_cast h1
  have hd : (0 : ℝ) < den := by exact_mod_cast h
  have ho : (0 : ℝ) < ONE := by exact_mod_cast ONE_pos
  rw [div_le_div_iff₀ hd ho]
  linarith

theorem cdiv_ge {a b : ℕ} (h : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  have h1 := cdiv_spec (a := a) h
  have h2 : (a : ℝ) ≤ (cdiv a b : ℝ) * b := by exact_mod_cast h1
  have hb : (0 : ℝ) < b := by exact_mod_cast h
  rw [div_le_iff₀ hb]
  exact h2

theorem mulUp_ge (x y : ℕ) : (x : ℝ) / ONE * ((y : ℝ) / ONE) ≤ (mulUp x y : ℝ) / ONE := by
  have h1 := mulUp_spec x y
  have h2 : (x : ℝ) * y ≤ (mulUp x y : ℝ) * ONE := by exact_mod_cast h1
  have ho : (0 : ℝ) < ONE := by exact_mod_cast ONE_pos
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) ho]
  nlinarith

theorem le_sqrtUp_sq (n : ℕ) : n ≤ sqrtUp n * sqrtUp n := by
  unfold sqrtUp
  dsimp only
  split_ifs with h
  · exact h.ge
  · exact (Nat.lt_succ_sqrt n).le

/-! ### `fac2`, `fac3`, `cTheta2`, `cTheta3`, `cTheta25` -/

theorem fac2_ge {q dn : ℕ} (hq : 2 ≤ q) (hdn : dn < DDEN) :
    1 + (DDEN : ℝ) / ((DDEN : ℝ) - dn) * (3 * q - 1) / ((q : ℝ) - 1) ^ 2 ≤
      (fac2 q dn : ℝ) / ONE := by
  rw [sqFactor_eq_ratio hq hdn]
  unfold fac2 nuDen
  have hd : 0 < (q - 1) * (q - 1) * (DDEN - dn) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  refine le_trans (le_of_eq ?_) (ratUp_ge hd)
  push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hdn.le,
    Nat.cast_sub (by omega : 1 ≤ 3 * q)]
  ring

theorem fac3_ge {q dn : ℕ} (hq : 2 ≤ q) (hdn : dn < DDEN) :
    1 + (DDEN : ℝ) / ((DDEN : ℝ) - dn) * (7 * (q : ℝ) ^ 2 - 2 * q + 1) / ((q : ℝ) - 1) ^ 3 ≤
      (fac3 q dn : ℝ) / ONE := by
  rw [cubeFactor_eq_ratio hq hdn]
  unfold fac3 nuDen
  have hd : 0 < (q - 1) * (q - 1) * (q - 1) * (DDEN - dn) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  refine le_trans (le_of_eq ?_) (ratUp_ge hd)
  have h7 : 2 * q ≤ 7 * q * q := by nlinarith
  push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hdn.le, Nat.cast_sub h7]
  ring

theorem cTheta2_ge {dn : ℕ} (hdn : 0 < dn) :
    (DDEN : ℝ) / (4 * dn) ≤ (cTheta2 dn : ℝ) / ONE := by
  unfold cTheta2
  have := ratUp_ge (num := DDEN) (den := 4 * dn) (by omega)
  push_cast at this
  exact this

theorem cTheta3_ge {dn : ℕ} (hdn : 0 < dn) :
    4 * (DDEN : ℝ) ^ 2 / (27 * (dn : ℝ) ^ 2) ≤ (cTheta3 dn : ℝ) / ONE := by
  unfold cTheta3
  have := ratUp_ge (num := 4 * DDEN * DDEN) (den := 27 * dn * dn) (by positivity)
  push_cast at this
  convert this using 2 <;> ring

/-- `cTheta25 dn / 2^62 = a·b` rounded up, with `a ≥ 6D/(25 dn)`, `b ≥ 0`, `b² ≥ 3D/(5 dn)`. -/
theorem cTheta25_ge {dn : ℕ} (hdn : 0 < dn) :
    ∃ a b : ℝ, 6 * (DDEN : ℝ) / (25 * dn) ≤ a ∧ 0 ≤ b ∧ 3 * (DDEN : ℝ) / (5 * dn) ≤ b ^ 2 ∧
      a * b ≤ (cTheta25 dn : ℝ) / ONE := by
  unfold cTheta25
  set a' := ratUp (6 * DDEN) (25 * dn)
  set b' := sqrtRatUp (3 * DDEN) (5 * dn)
  refine ⟨(a' : ℝ) / ONE, (b' : ℝ) / ONE, ?_, by positivity, ?_, mulUp_ge a' b'⟩
  · have := ratUp_ge (num := 6 * DDEN) (den := 25 * dn) (by omega)
    push_cast at this
    exact this
  · have ho : (0 : ℝ) < ONE := by exact_mod_cast ONE_pos
    have h1 : 3 * DDEN * ONE * ONE ≤ cdiv (3 * DDEN * ONE * ONE) (5 * dn) * (5 * dn) :=
      cdiv_spec (by omega)
    have h2 : cdiv (3 * DDEN * ONE * ONE) (5 * dn) ≤ b' * b' := le_sqrtUp_sq _
    have h3 : (3 * DDEN * ONE * ONE : ℝ) ≤ ((b' * b' : ℕ) : ℝ) * (5 * dn) := by
      have := Nat.mul_le_mul_right (5 * dn) h2
      have h4 := le_trans h1 this
      exact_mod_cast h4
    push_cast at h3
    have hdn' : (0 : ℝ) < dn := by exact_mod_cast hdn
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-! ### `blockVal` -/

theorem TWO32_real : (TWO32 : ℝ) = 2 ^ 32 := by rw [TWO32_eq]; norm_num

/-- Helper: `x·y·D ≤ K·(L·o)` ⟹ `(x/o)(y/o)·D/L ≤ K/o`. -/
theorem div_bound_helper {x y D K L o : ℝ} (ho : 0 < o) (hL : 0 < L)
    (h : x * y * D ≤ K * (L * o)) : x / o * (y / o) * D / L ≤ K / o := by
  rw [div_le_div_iff₀ hL ho]
  have e : x / o * (y / o) * D * o = x * y * D / o := by field_simp
  rw [e, div_le_iff₀ ho]
  linarith

/-- **The per-prime value of a block** (`CheckerImpl.blockVal`): for a prime `p` of the block
starting at `B` (`2 ≤ B ≤ p`), `δ_p = dn/10^9 ∈ (0, 1)`, per-prime factor bounds `B2`, `B25`, `B3`
(every cap) whose products over the primes below `p` are at most `ET2/2^62`, `ET25/2^62`,
`ET3/2^62`: `hingeLoss m δ p γ ≤ blockVal B dn ET2 ET25 ET3 / 2^62`. -/
theorem hingeLoss_le_blockVal {m p B dn : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hB : 2 ≤ B)
    (hBp : B ≤ p) (hδp : δ p = (dn : ℝ) / DDEN) (hdn0 : 0 < dn) (hdnD : dn < DDEN)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q ≤ 1) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ Nat.primesBelow p, tilt δ q ≤ ν q ∧ ν q ≤ q) (B2 B25 B3 : ℕ → ℝ)
    (hB2 : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ B2 q)
    (hB25 : ∀ q ∈ Nat.primesBelow p, ∀ γ,
      expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤ B25 q)
    (hB3 : ∀ q ∈ Nat.primesBelow p, ∀ γ, expect1 q (ν q) γ (fun a => ((a : ℝ) + 1) ^ 3) ≤ B3 q)
    {ET2 ET25 ET3 : ℕ} (hET2 : ∏ q ∈ Nat.primesBelow p, B2 q ≤ (ET2 : ℝ) / ONE)
    (hET25 : ∏ q ∈ Nat.primesBelow p, B25 q ≤ (ET25 : ℝ) / ONE)
    (hET3 : ∏ q ∈ Nat.primesBelow p, B3 q ≤ (ET3 : ℝ) / ONE) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ (blockVal B dn ET2 ET25 ET3 : ℝ) / ONE := by
  have ho : (0 : ℝ) < ONE := by exact_mod_cast ONE_pos
  have hdn' : (0 : ℝ) < dn := by exact_mod_cast hdn0
  have hd : (dn : ℝ) < DDEN := by exact_mod_cast hdnD
  have hDd : (0 : ℝ) < (DDEN : ℝ) - dn := by linarith
  have hB1 : (0 : ℝ) < (B : ℝ) - 1 := by
    have : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hpm : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ B)]; simp
  have hnd : ((DDEN - dn : ℕ) : ℝ) = (DDEN : ℝ) - dn := by
    rw [Nat.cast_sub hdnD.le]
  unfold blockVal nuDen
  simp only
  rw [Nat.cast_min, Nat.cast_min, ← min_div_div_right ho.le, ← min_div_div_right ho.le]
  refine le_min ?_ (le_min ?_ ?_)
  · -- θ = 2
    have h := hingeLoss_le_blockVal_two (m := m) hp hB hBp hδp hdn0 hdnD hδ hν B2 hB2 hET2
      (cTheta2_ge hdn0) γ
    refine h.trans ?_
    set K := cdiv (cTheta2 dn * ET2 * DDEN) ((B - 1) * (B - 1) * (DDEN - dn) * ONE) with hK
    have hden : 0 < (B - 1) * (B - 1) * (DDEN - dn) * ONE :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) ONE_pos
    have hc := cdiv_spec (a := cTheta2 dn * ET2 * DDEN) hden
    rw [← hK] at hc
    have hc' : ((cTheta2 dn * ET2 * DDEN : ℕ) : ℝ) ≤
        (K : ℝ) * (((B - 1) * (B - 1) * (DDEN - dn) * ONE : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast [hpm, hnd] at hc'
    refine div_bound_helper ho (by positivity) ?_
    calc (cTheta2 dn : ℝ) * ET2 * DDEN ≤ K * ((B - 1) * (B - 1) * (DDEN - dn) * ONE) := hc'
      _ = K * (((B : ℝ) - 1) ^ 2 * ((DDEN : ℝ) - dn) * ONE) := by ring
  · -- θ = 5/2
    obtain ⟨a, b, ha, hb0, hb, hab⟩ := cTheta25_ge hdn0
    set sq := Nat.sqrt ((B - 1) * TWO32 * TWO32) with hsq_def
    have hsq : sq * sq ≤ (B - 1) * 2 ^ 64 := by
      have := Nat.sqrt_le ((B - 1) * TWO32 * TWO32)
      rw [← hsq_def, TWO32_eq] at this
      calc sq * sq ≤ (B - 1) * 2 ^ 32 * 2 ^ 32 := this
        _ = (B - 1) * 2 ^ 64 := by ring
    have hsq0 : 0 < sq := by
      rw [hsq_def]
      exact Nat.sqrt_pos.2 (Nat.mul_pos (Nat.mul_pos (by omega) (by decide)) (by decide))
    clear_value sq
    have h := hingeLoss_le_blockVal_five_halves (m := m) hp hB hBp hδp hdn0 hdnD hδ hν B25
      hB25 hET25 ha hb0 hb hab hsq0 hsq γ
    refine h.trans ?_
    set K := cdiv (cTheta25 dn * ET25 * DDEN * TWO32) ((B - 1) * (B - 1) * sq * (DDEN - dn) * ONE)
      with hK
    have hden : 0 < (B - 1) * (B - 1) * sq * (DDEN - dn) * ONE :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hsq0)
        (by omega)) ONE_pos
    have hc := cdiv_spec (a := cTheta25 dn * ET25 * DDEN * TWO32) hden
    rw [← hK, TWO32_eq] at hc
    have hc' : (cTheta25 dn : ℝ) * ET25 * DDEN * 2 ^ 32 ≤
        (K : ℝ) * (((B : ℝ) - 1) ^ 2 * sq * ((DDEN : ℝ) - dn) * ONE) := by
      have h1 := (Nat.cast_le (α := ℝ)).2 hc
      push_cast [hpm, hnd] at h1
      have e2 : (K : ℝ) * (((B : ℝ) - 1) * ((B : ℝ) - 1) * sq * ((DDEN : ℝ) - dn) * ONE) =
          (K : ℝ) * (((B : ℝ) - 1) ^ 2 * sq * ((DDEN : ℝ) - dn) * ONE) := by ring
      linarith
    have hsq' : (0 : ℝ) < sq := by exact_mod_cast hsq0
    have e : (cTheta25 dn : ℝ) / ONE * ((ET25 : ℝ) / ONE) * DDEN * 2 ^ 32 =
        (cTheta25 dn : ℝ) / ONE * ((ET25 : ℝ) / ONE) * (DDEN * 2 ^ 32) := by ring
    rw [e]
    refine div_bound_helper ho (mul_pos (mul_pos (pow_pos hB1 2) hsq') hDd) ?_
    have e3 : (cTheta25 dn : ℝ) * ET25 * (DDEN * 2 ^ 32) = (cTheta25 dn : ℝ) * ET25 * DDEN * 2 ^ 32 :=
      by ring
    have e4 : (K : ℝ) * (((B : ℝ) - 1) ^ 2 * sq * ((DDEN : ℝ) - dn) * ONE) =
        (K : ℝ) * (((B : ℝ) - 1) ^ 2 * sq * ((DDEN : ℝ) - dn) * ONE) := rfl
    linarith
  · -- θ = 3
    have h := hingeLoss_le_blockVal_three (m := m) hp hB hBp hδp hdn0 hdnD hδ hν B3 hB3 hET3
      (cTheta3_ge hdn0) γ
    refine h.trans ?_
    set K := cdiv (cTheta3 dn * ET3 * DDEN) ((B - 1) * (B - 1) * (B - 1) * (DDEN - dn) * ONE)
      with hK
    have hden : 0 < (B - 1) * (B - 1) * (B - 1) * (DDEN - dn) * ONE :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
        (by omega)) ONE_pos
    have hc := cdiv_spec (a := cTheta3 dn * ET3 * DDEN) hden
    rw [← hK] at hc
    have hc' : ((cTheta3 dn * ET3 * DDEN : ℕ) : ℝ) ≤
        (K : ℝ) * (((B - 1) * (B - 1) * (B - 1) * (DDEN - dn) * ONE : ℕ) : ℝ) := by
      exact_mod_cast hc
    push_cast [hpm, hnd] at hc'
    refine div_bound_helper ho (by positivity) ?_
    calc (cTheta3 dn : ℝ) * ET3 * DDEN ≤ K * ((B - 1) * (B - 1) * (B - 1) * (DDEN - dn) * ONE) := hc'
      _ = K * (((B : ℝ) - 1) ^ 3 * ((DDEN : ℝ) - dn) * ONE) := by ring

/-! ### `fac2`, `fac3`, `fac25` as uniform bounds on `E_γ[(v+1)^θ]` (block form) -/

/-- `fac2 Q dn / 2^62` bounds `E_{q,ν,γ}[(v+1)²]` for every prime `q ≥ Q` of a block with tilt
`ν ≤ 10^9/(10^9 - dn)`, every cap. -/
theorem expect1_sq_le_fac2 {q Q dn : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hdn : dn < DDEN) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn)) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 2) ≤ (fac2 Q dn : ℝ) / ONE :=
  (expect1_sq_le_of_le (by omega) hQq hν0 hν γ).trans (fac2_ge hQ hdn)

/-- `fac3 Q dn / 2^62` bounds `E_{q,ν,γ}[(v+1)³]` (block form). -/
theorem expect1_cube_le_fac3 {q Q dn : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hdn : dn < DDEN) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn)) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ 3) ≤ (fac3 Q dn : ℝ) / ONE :=
  (expect1_cube_le_of_le (by omega) hQq hν0 hν γ).trans (fac3_ge hQ hdn)

/-- The tail factor is bounded by `fac2` at the block start: `tailFactor δ q ≤ fac2 Q dn / 2^62`. -/
theorem tailFactor_le_fac2 {δ : ℕ → ℝ} {q Q dn : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hdn : dn < DDEN)
    (hδq : δ q ≤ 1) (htilt : tilt δ q ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn)) :
    tailFactor δ q ≤ (fac2 Q dn : ℝ) / ONE :=
  (tailFactor_le_block hQ hQq hδq htilt).trans (fac2_ge hQ hdn)

theorem sqrtUp_le_of_le_sq {n m : ℕ} (h : n ≤ m * m) : sqrtUp n ≤ m := by
  unfold sqrtUp
  dsimp only
  have hs : Nat.sqrt n ≤ m := by
    have := Nat.sqrt_le_sqrt h
    rwa [Nat.sqrt_eq] at this
  split_ifs with h2
  · exact hs
  · rcases Nat.lt_or_ge (Nat.sqrt n) m with h3 | h3
    · omega
    · have h4 : Nat.sqrt n = m := le_antisymm hs h3
      exfalso
      apply h2
      apply le_antisymm (Nat.sqrt_le n)
      rw [h4]
      exact h

/-- `sqrt32Up b ≤ b · 2^32` for `b ≥ 1` (so the checker's `b·2^32 - sqrt32Up b` is exact). -/
theorem sqrt32Up_le {b : ℕ} (hb : 1 ≤ b) : sqrt32Up b ≤ b * TWO32 := by
  unfold sqrt32Up
  apply sqrtUp_le_of_le_sq
  calc b * TWO32 * TWO32 = b * (TWO32 * TWO32) := by ring
    _ ≤ (b * b) * (TWO32 * TWO32) := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left b (by omega))
    _ = b * TWO32 * (b * TWO32) := by ring

/-- `(sqrt32Up b / 2^32)² ≥ b`. -/
theorem le_sqrt32Up_sq (b : ℕ) : (b : ℝ) ≤ ((sqrt32Up b : ℝ) / 2 ^ 32) ^ 2 := by
  unfold sqrt32Up
  have h := le_sqrtUp_sq (b * TWO32 * TWO32)
  have h' : ((b * TWO32 * TWO32 : ℕ) : ℝ) ≤ ((sqrtUp (b * TWO32 * TWO32) *
      sqrtUp (b * TWO32 * TWO32) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast [TWO32_real] at h'
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith

/-- The real terms subtracted by `fac25Sub`: `k(i) = q^{-i}((i+1)³ - (i+1)² s(i+1))`,
`s(b) = sqrt32Up b / 2^32`. -/
noncomputable def fac25Term (q i : ℕ) : ℝ :=
  ((q : ℝ)⁻¹) ^ i * (((i : ℝ) + 1) ^ 3 - ((i : ℝ) + 1) ^ 2 * ((sqrt32Up (i + 1) : ℝ) / 2 ^ 32))

/-- **Loop bound for `fac25Sub`** (started at `a ≥ 1` with `qa = q^a`): the result is at most
`acc + 2^62 · Σ_{i ∈ [a, A)} k(i)` for some `A ≥ a` (each term is rounded down). -/
theorem fac25Sub_le {q : ℕ} (hq : 1 ≤ q) (fuel : ℕ) :
    ∀ a acc : ℕ, 1 ≤ a → ∃ A, a ≤ A ∧
      (fac25Sub q a (q ^ a) acc fuel : ℝ) ≤ acc + ONE * ∑ i ∈ Ico a A, fac25Term q i := by
  induction fuel with
  | zero =>
    intro a acc _
    refine ⟨a, le_rfl, ?_⟩
    rw [fac25Sub]
    simp
  | succ f ih =>
    intro a acc ha
    rw [fac25Sub]
    split_ifs with hbig
    · exact ⟨a, le_rfl, by simp⟩
    · rw [← pow_succ]
      set t := (a + 1) * (a + 1) * ((a + 1) * TWO32 - sqrt32Up (a + 1)) * ONE / (TWO32 * q ^ a)
        with ht
      obtain ⟨A, hA, hle⟩ := ih (a + 1) (acc + t) (by omega)
      refine ⟨A, by omega, ?_⟩
      have hqa : (0 : ℝ) < (q : ℝ) ^ a := by
        have : (0 : ℝ) < q := by exact_mod_cast hq
        positivity
      have htle : (t : ℝ) ≤ ONE * fac25Term q a := by
        have h1 : (t : ℝ) ≤ (((a + 1) * (a + 1) * ((a + 1) * TWO32 - sqrt32Up (a + 1)) * ONE : ℕ) : ℝ) /
            ((TWO32 * q ^ a : ℕ) : ℝ) := Nat.cast_div_le
        have hs := sqrt32Up_le (b := a + 1) (by omega)
        push_cast [Nat.cast_sub hs, TWO32_real] at h1
        refine h1.trans (le_of_eq ?_)
        unfold fac25Term
        rw [inv_pow]
        field_simp
      have hsum : ∑ i ∈ Ico a A, fac25Term q i = fac25Term q a + ∑ i ∈ Ico (a + 1) A, fac25Term q i :=
        sum_eq_sum_Ico_succ_bot (by omega) _
      rw [hsum]
      push_cast at hle
      nlinarith [hle, htle]

/-- **`fac25`, block form**: `fac25 Q dn / 2^62` bounds `E_{q,ν,γ}[(v+1)^{5/2}]` for every prime
`q ≥ Q` with tilt `0 ≤ ν ≤ 10^9/(10^9 - dn) ≤ Q`, every cap. -/
theorem expect1_five_halves_le_fac25 {q Q dn : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hdn : dn < DDEN)
    (hDQ : (DDEN : ℝ) / ((DDEN : ℝ) - dn) ≤ Q) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν ≤ (DDEN : ℝ) / ((DDEN : ℝ) - dn)) (γ : ℕ) :
    expect1 q ν γ (fun a => ((a : ℝ) + 1) ^ (5 / 2 : ℝ)) ≤ (fac25 Q dn : ℝ) / ONE := by
  have ho : (0 : ℝ) < ONE := by exact_mod_cast ONE_pos
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : (dn : ℝ) < DDEN := by exact_mod_cast hdn
  have hDd : (0 : ℝ) < (DDEN : ℝ) - dn := by linarith
  -- the loop
  obtain ⟨A, hA, hS⟩ := fac25Sub_le (q := Q) (by omega) 128 1 0 le_rfl
  rw [pow_one] at hS
  set S := fac25Sub Q 1 Q 0 128 with hSdef
  -- s3
  set s3 := cdiv (Q * (7 * Q * Q - 2 * Q + 1) * ONE) ((Q - 1) * (Q - 1) * (Q - 1) * (Q - 1))
    with hs3
  have h7 : 2 * Q ≤ 7 * Q * Q := by nlinarith
  have hQ1 : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ Q)]; simp
  have hs3ge : (Q : ℝ) * (7 * (Q : ℝ) ^ 2 - 2 * Q + 1) / ((Q : ℝ) - 1) ^ 4 * ONE ≤ s3 := by
    have hden : 0 < (Q - 1) * (Q - 1) * (Q - 1) * (Q - 1) :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
    have := cdiv_ge (a := Q * (7 * Q * Q - 2 * Q + 1) * ONE) hden
    push_cast [Nat.cast_sub h7, hQ1] at this
    refine le_trans (le_of_eq ?_) this
    ring
  -- W
  set Wn := s3 - S with hWn
  have hW : (s3 : ℝ) - S ≤ Wn := by
    rw [hWn]
    rcases le_total S s3 with h | h
    · rw [Nat.cast_sub h]
    · have : s3 - S = 0 := Nat.sub_eq_zero_of_le h
      rw [this]
      have : (s3 : ℝ) ≤ S := by exact_mod_cast h
      push_cast
      linarith
  -- the exact form
  have hIco : Ico 1 A = Icc 1 (A - 1) := by
    ext i
    simp only [mem_Ico, mem_Icc]
    omega
  have hWreal : (Q : ℝ) * (7 * (Q : ℝ) ^ 2 - 2 * Q + 1) / ((Q : ℝ) - 1) ^ 4 -
      ∑ a ∈ Icc 1 (A - 1), ((Q : ℝ)⁻¹) ^ a *
        (((a : ℝ) + 1) ^ 3 - ((a : ℝ) + 1) ^ 2 * ((sqrt32Up (a + 1) : ℝ) / 2 ^ 32)) ≤
      (Wn : ℝ) / ONE := by
    rw [le_div_iff₀ ho]
    have e : ∑ a ∈ Icc 1 (A - 1), ((Q : ℝ)⁻¹) ^ a *
        (((a : ℝ) + 1) ^ 3 - ((a : ℝ) + 1) ^ 2 * ((sqrt32Up (a + 1) : ℝ) / 2 ^ 32)) =
        ∑ i ∈ Ico 1 A, fac25Term Q i := by
      rw [hIco]
      rfl
    rw [e]
    push_cast at hS
    nlinarith [hS, hs3ge, hW]
  have h1 := expect1_five_halves_le_ratio hQ hQq hdn hDQ hν0 hν (A - 1)
    (fun b => (sqrt32Up b : ℝ) / 2 ^ 32) (fun a _ => by positivity)
    (fun a _ => by exact_mod_cast le_sqrt32Up_sq (a + 1)) hWreal γ
  refine h1.trans ?_
  -- fac25 = ONE + cdiv (DDEN (Q-1) W) ((DDEN - dn) Q)
  unfold fac25 nuDen
  simp only
  rw [← hs3, ← hSdef, ← hWn]
  have hden : 0 < (DDEN - dn) * Q := Nat.mul_pos (by omega) (by omega)
  have hc := cdiv_ge (a := DDEN * (Q - 1) * Wn) hden
  have hnd : ((DDEN - dn : ℕ) : ℝ) = (DDEN : ℝ) - dn := by rw [Nat.cast_sub hdn.le]
  push_cast [hQ1, hnd] at hc
  push_cast
  rw [add_div, div_self ho.ne']
  have hQ0 : (0 : ℝ) < Q := by linarith
  have e : (DDEN : ℝ) * ((Q : ℝ) - 1) * ((Wn : ℝ) / ONE) / (((DDEN : ℝ) - dn) * Q) =
      (DDEN : ℝ) * ((Q : ℝ) - 1) * Wn / (((DDEN : ℝ) - dn) * Q) / ONE := by
    field_simp
  rw [e]
  have := div_le_div_of_nonneg_right hc ho.le
  linarith

/-! ### `firstMoment` -/

theorem strip_spec (q : ℕ) : ∀ (f x : ℕ), ∃ k, x = isSmoothOver.strip q x f * q ^ k := by
  intro f
  induction f with
  | zero => intro x; exact ⟨0, by rw [isSmoothOver.strip]; simp⟩
  | succ f ih =>
    intro x
    rw [isSmoothOver.strip]
    split_ifs with h
    · obtain ⟨k, hk⟩ := ih (x / q)
      refine ⟨k + 1, ?_⟩
      have hq : q ∣ x := Nat.dvd_of_mod_eq_zero (by simpa using h)
      calc x = q * (x / q) := (Nat.mul_div_cancel' hq).symm
        _ = q * (isSmoothOver.strip q (x / q) f * q ^ k) := by rw [← hk]
        _ = isSmoothOver.strip q (x / q) f * q ^ (k + 1) := by ring
    · exact ⟨0, by simp⟩

/-- Soundness of the smoothness test: every prime factor of `x` divides one of the entries
`ps[j]`, `i ≤ j < i + fuel` (when `i + fuel ≤ ps.size`). -/
theorem isSmoothOver_go_sound (ps : Array ℕ) : ∀ (fuel i x : ℕ), i + fuel ≤ ps.size →
    isSmoothOver.go ps i x fuel = true → ∀ r, r.Prime → r ∣ x →
      ∃ j, i ≤ j ∧ j < i + fuel ∧ r ∣ ps[j]! := by
  intro fuel
  induction fuel with
  | zero =>
    intro i x _ h r hr hrx
    rw [isSmoothOver.go] at h
    have hx : x = 1 := by simpa using h
    rw [hx] at hrx
    exact absurd (Nat.le_of_dvd one_pos hrx) (by have := hr.two_le; omega)
  | succ f ih =>
    intro i x hsz h r hr hrx
    rw [isSmoothOver.go] at h
    obtain ⟨k, hk⟩ := strip_spec ps[i]! 64 x
    rw [hk] at hrx
    rcases (Nat.Prime.dvd_mul hr).1 hrx with h1 | h1
    · obtain ⟨j, hj1, hj2, hj3⟩ := ih (i + 1) _ (by omega) h r hr h1
      exact ⟨j, by omega, by omega, hj3⟩
    · exact ⟨i, le_rfl, by omega, hr.dvd_of_dvd_pow h1⟩

theorem isSmoothOver_sound {ps : Array ℕ} {n : ℕ} (h : isSmoothOver ps n = true) {r : ℕ}
    (hr : r.Prime) (hrn : r ∣ n) : ∃ j, j < ps.size ∧ r ∣ ps[j]! := by
  rw [isSmoothOver] at h
  obtain ⟨j, -, hj, hdvd⟩ := isSmoothOver_go_sound ps ps.size 0 n (by omega) h r hr hrn
  exact ⟨j, by omega, hdvd⟩

/-- Soundness of `numThresholdsAbove`: if `J ≠ 0` then `n < ⌈m/p^J⌉`, hence `n·p^J < m`. -/
theorem numThresholdsAbove_go_sound {m p n : ℕ} : ∀ (fuel acc : ℕ),
    (acc ≠ 0 → n < cdiv m (p ^ acc)) →
      (numThresholdsAbove.go m p n (p ^ (acc + 1)) acc fuel ≠ 0 →
        n < cdiv m (p ^ numThresholdsAbove.go m p n (p ^ (acc + 1)) acc fuel)) := by
  intro fuel
  induction fuel with
  | zero => intro acc h; rw [numThresholdsAbove.go]; exact h
  | succ f ih =>
    intro acc h
    rw [numThresholdsAbove.go]
    split_ifs with h1
    · rw [← pow_succ]
      exact ih (acc + 1) (fun _ => h1)
    · exact h

theorem mul_lt_of_lt_cdiv {n m b : ℕ} (hb : 0 < b) (h : n < cdiv m b) : n * b < m := by
  unfold cdiv at h
  have h1 : (n + 1) * b ≤ (m + b - 1) / b * b := Nat.mul_le_mul_right b h
  have h2 : (m + b - 1) / b * b ≤ m + b - 1 := Nat.div_mul_le_self _ _
  have : (n + 1) * b = n * b + b := by ring
  omega

theorem numThresholdsAbove_sound {m p n : ℕ} (hp : 0 < p) (h : numThresholdsAbove m p n ≠ 0) :
    n * p ^ numThresholdsAbove m p n < m := by
  rw [numThresholdsAbove] at h ⊢
  have := numThresholdsAbove_go_sound (m := m) (p := p) (n := n) 64 0 (fun h0 => absurd rfl h0)
  rw [zero_add, pow_one] at this
  exact mul_lt_of_lt_cdiv (by positivity) (this h)

/-- The subtraction loop of `firstMoment`. -/
theorem firstMoment_go_eq (m p : ℕ) (ps : Array ℕ) : ∀ (fuel n acc : ℕ),
    firstMoment.go m p ps n fuel acc = acc + ∑ i ∈ Ico n (n + fuel),
      (if isSmoothOver ps i = true then
        (p ^ numThresholdsAbove m p i - 1) * ONE / ((p - 1) * p ^ numThresholdsAbove m p i * i)
      else 0) := by
  intro fuel
  induction fuel with
  | zero => intro n acc; rw [firstMoment.go]; simp
  | succ f ih =>
    intro n acc
    rw [firstMoment.go, sum_eq_sum_Ico_succ_bot (by omega)]
    split_ifs with h
    · rw [ih (n + 1), show n + 1 + f = n + (f + 1) by ring]
      ring
    · rw [ih (n + 1), show n + 1 + f = n + (f + 1) by ring]
      simp

theorem foldl_mul_eq_prod (f : ℕ → ℕ) : ∀ (l : List ℕ) (b : ℕ),
    List.foldl (fun a q => a * f q) b l = b * (l.map f).prod := by
  intro l
  induction l with
  | nil => intro b; simp
  | cons x l ih => intro b; simp [ih]; ring

theorem array_foldl_eq_prod {ps : Array ℕ} {S : Finset ℕ} (hnd : ps.toList.Nodup)
    (hmem : ∀ q, q ∈ ps.toList ↔ q ∈ S) (f : ℕ → ℕ) :
    ps.foldl (fun a q => a * f q) 1 = ∏ q ∈ S, f q := by
  classical
  rw [← Array.foldl_toList, foldl_mul_eq_prod, one_mul, ← List.prod_toFinset f hnd]
  congr 1
  ext q
  rw [List.mem_toFinset, hmem]

/-- **`firstMoment`**: for a prime `p` with `δ_q = 0` for every `q ≤ p`, and `ps` a duplicate-free
array whose entries are exactly the primes below `p` (e.g. `primes.extract 0 k`), for every cap
`γ`: `hingeLoss m δ p γ ≤ firstMoment m p ps / 2^62`. -/
theorem hingeLoss_le_firstMoment_impl {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hδp : δ p = 0)
    (hδ : ∀ q ∈ Nat.primesBelow p, δ q = 0) (ps : Array ℕ) (hnd : ps.toList.Nodup)
    (hmem : ∀ q, q ∈ ps.toList ↔ q ∈ Nat.primesBelow p) (γ : ℕ → ℕ) :
    hingeLoss m δ p γ ≤ (firstMoment m p ps : ℝ) / ONE := by
  classical
  have ho : (0 : ℝ) < ONE := by exact_mod_cast ONE_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set D := (Ico 1 (cdiv m p)).filter (fun n => isSmoothOver ps n = true) with hD
  set J := numThresholdsAbove m p with hJ
  have hDmem : ∀ n ∈ D, 0 < n ∧ ∀ r ∈ n.primeFactors, r < p := by
    intro n hn
    rw [hD, mem_filter, mem_Ico] at hn
    refine ⟨by omega, fun r hr => ?_⟩
    have hrp := Nat.prime_of_mem_primeFactors hr
    obtain ⟨j, hj, hdvd⟩ := isSmoothOver_sound hn.2 hrp (Nat.dvd_of_mem_primeFactors hr)
    have hmemj : ps[j]! ∈ ps.toList := by
      rw [getElem!_pos ps j hj]
      exact Array.getElem_mem_toList hj
    have hq := (hmem _).1 hmemj
    rw [Nat.mem_primesBelow] at hq
    have : r = ps[j]! := (Nat.prime_dvd_prime_iff_eq hrp hq.2).1 hdvd
    rw [this]
    exact hq.1
  have hJs : ∀ n ∈ D, J n ≠ 0 → n * p ^ J n < m := fun n _ h =>
    numThresholdsAbove_sound hp.pos h
  refine (hingeLoss_le_firstMoment_of_zero hp hδp hδ D hDmem J hJs γ).trans ?_
  -- the checker's value
  rw [firstMoment]
  rw [array_foldl_eq_prod hnd hmem (fun q => q), array_foldl_eq_prod hnd hmem (fun q => q - 1),
    firstMoment_go_eq]
  set T1 := cdiv ((∏ q ∈ Nat.primesBelow p, q) * ONE) ((∏ q ∈ Nat.primesBelow p, (q - 1)) * (p - 1))
    with hT1
  set G := 0 + ∑ i ∈ Ico 1 (1 + (cdiv m p - 1)), (if isSmoothOver ps i = true then
      (p ^ numThresholdsAbove m p i - 1) * ONE / ((p - 1) * p ^ numThresholdsAbove m p i * i)
      else 0) with hG
  -- (T1 - G : ℕ) ≥ T1 - G (reals)
  have hsub : (T1 : ℝ) - G ≤ ((T1 - G : ℕ) : ℝ) := by
    rcases le_total G T1 with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]
      have : (T1 : ℝ) ≤ G := by exact_mod_cast h
      push_cast
      linarith
  have hprim : ∀ q ∈ Nat.primesBelow p, 1 ≤ q := fun q hq =>
    (Nat.prime_of_mem_primesBelow hq).one_lt.le
  -- T1 / ONE ≥ Π q / (Π (q - 1) (p - 1))
  have hT1 : (∏ q ∈ Nat.primesBelow p, (q : ℝ)) /
      ((∏ q ∈ Nat.primesBelow p, ((q : ℝ) - 1)) * ((p : ℝ) - 1)) ≤ (T1 : ℝ) / ONE := by
    have hden : 0 < (∏ q ∈ Nat.primesBelow p, (q - 1)) * (p - 1) := by
      refine Nat.mul_pos (prod_pos fun q hq => ?_) (by have := hp.two_le; omega)
      have := (Nat.prime_of_mem_primesBelow hq).two_le
      omega
    have := ratUp_ge (num := ∏ q ∈ Nat.primesBelow p, q) hden
    unfold ratUp at this
    rw [← hT1] at this
    refine le_trans (le_of_eq ?_) this
    push_cast [Nat.cast_prod, Nat.cast_sub (hp.one_lt.le)]
    congr 2
    exact prod_congr rfl fun q hq => by rw [Nat.cast_sub (hprim q hq)]; simp
  -- G / ONE ≤ Σ_{n ∈ D} (p^J - 1)/((p-1) p^J n)
  have hIco : Ico 1 (1 + (cdiv m p - 1)) = Ico 1 (cdiv m p) := by
    ext i; simp only [mem_Ico]; omega
  have hG' : (G : ℝ) / ONE ≤ ∑ n ∈ D, ((p : ℝ) ^ J n - 1) / (((p : ℝ) - 1) * (p : ℝ) ^ J n * n) := by
    rw [hG, zero_add, hIco, ← sum_filter, ← hD]
    push_cast
    rw [Finset.sum_div]
    refine sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := by rw [hD, mem_filter, mem_Ico] at hn; omega
    have hpJ : 1 ≤ p ^ J n := Nat.one_le_pow _ _ hp.pos
    have hden : 0 < (p - 1) * p ^ J n * n :=
      Nat.mul_pos (Nat.mul_pos (by have := hp.two_le; omega) (by omega)) hn0
    have h1 : (((p ^ J n - 1) * ONE / ((p - 1) * p ^ J n * n) : ℕ) : ℝ) ≤
        (((p ^ J n - 1) * ONE : ℕ) : ℝ) / (((p - 1) * p ^ J n * n : ℕ) : ℝ) := Nat.cast_div_le
    rw [div_le_iff₀ ho]
    refine h1.trans (le_of_eq ?_)
    push_cast [Nat.cast_sub hpJ, Nat.cast_sub hp.one_lt.le]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hpJ' : (0 : ℝ) < (p : ℝ) ^ J n := by positivity
    have hp' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    field_simp
  have hfin := div_le_div_of_nonneg_right hsub ho.le
  rw [sub_div] at hfin
  linarith

end MinModulus.CheckerMath
