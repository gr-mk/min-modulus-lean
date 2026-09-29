import MinModulus.Checker2Sound.Defs
import MinModulus.CheckerSound.Loop
import MinModulus.CheckerSound.MomentCode

/-!
# `Checker2Sound.LoopBasic`: helpers for the loops of `run2` (L2-E)

STATUS: complete (fully proved). Owned by L2-E (namespace `MinModulus.Checker2Sound.E`).

* P-values: `pv_nonneg`, `pv_add`, `pv_mono`, `pv_ONE`, `pv_zero`, `pv_mul_le_mulUp`,
  `pv_mulUp_le`, `pv_powUp`, `pv_eq_div_ONE` (transferred from the first proof's `pv`, which is
  the same function `x / 2^62`).
* The certificate's δ (`delta2 P = deltaPairR (deltaCert2 P)`): `deltaCert2_of_le/_of_gt`,
  `two_mul_deltaCert2_le`, `delta2_of_le/_of_gt`, `delta2_nonneg`, `delta2_le_half`,
  `delta2_eq_zero_iff`, `nu2_eq` (the exact tilt `10^9/(10^9 − deltaN2 P q)`), and the
  per-prime factor of `T`: `tailFactor_le_fac2'` (`Q ≤ q`), `one_le_tailFactor2`.
* The schedule is constant on `(PX, ∞)` under `schedOk` and `kps[0] ≤ PX`: `deltaN2_eq_of_gt`.
* `cdiv_le_two_iff` (`⌈m/p⌉ ≤ 2 ↔ m ≤ 2p`).
* The array of primes: `primes2_toList` (reusing `CheckerSound.A.primesUpTo_toList` and the
  array lemmas of `CheckerSound.D`), `dns2_get!`.
-/

namespace MinModulus.Checker2Sound.E

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath MinModulus.Main

/-! ## P-values -/

theorem pv_eq_CS (x : ℕ) : pv x = MinModulus.CheckerSound.pv x := rfl

theorem pv_nonneg (x : ℕ) : 0 ≤ pv x := MinModulus.CheckerSound.pv_nonneg x

theorem pv_add (x y : ℕ) : pv (x + y) = pv x + pv y := MinModulus.CheckerSound.pv_add x y

theorem pv_mono {x y : ℕ} (h : x ≤ y) : pv x ≤ pv y := MinModulus.CheckerSound.pv_mono h

theorem pv_ONE : pv ONE = 1 := MinModulus.CheckerSound.pv_ONE

theorem pv_zero : pv 0 = 0 := MinModulus.CheckerSound.pv_zero

theorem pv_mul_le_mulUp (x y : ℕ) : pv x * pv y ≤ pv (mulUp x y) :=
  MinModulus.CheckerSound.pv_mul_le_mulUp x y

theorem pv_mulUp_le {x y : ℕ} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ pv x)
    (hb : b ≤ pv y) : a * b ≤ pv (mulUp x y) :=
  MinModulus.CheckerSound.A.pv_mulUp_le ha0 hb0 ha hb

theorem pv_powUp (x n : ℕ) : pv x ^ n ≤ pv (powUp x n) := MinModulus.CheckerSound.A.pv_powUp x n

theorem pv_eq_div_ONE (x : ℕ) : pv x = (x : ℝ) / ONE := MinModulus.CheckerSound.A.pv_eq_div_ONE x

theorem pv_mul_nat (n x : ℕ) : pv (n * x) = (n : ℝ) * pv x := by
  unfold pv; push_cast; ring

/-! ## The certificate's δ -/

theorem DDEN_real : ((DDEN : ℕ) : ℝ) = 10 ^ 9 := by norm_num [DDEN]

theorem deltaN2_lt_DDEN (P : Params2) (p : ℕ) : deltaN2 P p < DDEN :=
  lt_of_le_of_lt (deltaN2_le P p) (by decide)

theorem deltaCert2_of_le {P : Params2} {p : ℕ} (h : p ≤ P.X) :
    deltaCert2 P p = (deltaN2 P p, DDEN) := by
  unfold deltaCert2
  simp only [show ¬ P.X < p from not_lt.2 h, ↓reduceIte]

theorem deltaCert2_of_gt {P : Params2} {p : ℕ} (h : P.X < p) : deltaCert2 P p = (1, 2) := by
  unfold deltaCert2
  simp only [h, ↓reduceIte]

theorem two_mul_deltaCert2_le (P : Params2) (p : ℕ) :
    2 * (deltaCert2 P p).1 ≤ (deltaCert2 P p).2 := by
  unfold deltaCert2
  split_ifs
  · decide
  · have h := deltaN2_le P p
    simp only [DNMAX2] at h
    simp only [DDEN]
    omega

theorem delta2_eq (P : Params2) : delta2 P = deltaPairR (deltaCert2 P) := rfl

theorem delta2_of_le {P : Params2} {p : ℕ} (h : p ≤ P.X) :
    delta2 P p = (deltaN2 P p : ℝ) / 10 ^ 9 := by
  rw [delta2_eq, deltaPairR_of_eq (deltaCert2_of_le h), DDEN_real]

theorem delta2_of_gt {P : Params2} {p : ℕ} (h : P.X < p) : delta2 P p = 1 / 2 := by
  rw [delta2_eq, deltaPairR_of_eq (deltaCert2_of_gt h)]
  norm_num

theorem delta2_nonneg (P : Params2) (p : ℕ) : 0 ≤ delta2 P p := by
  rw [delta2_eq, deltaPairR_apply]
  positivity

theorem delta2_le_half (P : Params2) (p : ℕ) : delta2 P p ≤ 1 / 2 := by
  rw [delta2_eq, deltaPairR_apply]
  have h := two_mul_deltaCert2_le P p
  have h' : (2 : ℝ) * (deltaCert2 P p).1 ≤ (deltaCert2 P p).2 := by exact_mod_cast h
  rcases Nat.eq_zero_or_pos (deltaCert2 P p).2 with h0 | hpos
  · rw [h0]; simp
  · have hpos' : (0 : ℝ) < (deltaCert2 P p).2 := by exact_mod_cast hpos
    rw [div_le_iff₀ hpos']
    linarith

theorem delta2_le_one (P : Params2) (p : ℕ) : delta2 P p ≤ 1 := by
  linarith [delta2_le_half P p]

theorem delta2_eq_zero_iff {P : Params2} {p : ℕ} (h : p ≤ P.X) :
    delta2 P p = 0 ↔ deltaN2 P p = 0 := by
  rw [delta2_of_le h]
  constructor
  · intro h0
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · exact_mod_cast h0
    · norm_num at h0
  · intro h0
    rw [h0]
    simp

/-- The exact tilt: `nu2 P q = 10^9/(10^9 − deltaN2 P q)` for `q ≤ X`. -/
theorem nu2_eq {P : Params2} {q : ℕ} (h : q ≤ P.X) :
    nu2 P q = (DDEN : ℝ) / ((DDEN : ℝ) - deltaN2 P q) := by
  unfold nu2
  rw [delta2_eq, tilt_deltaPairR (deltaCert2_of_le h) (deltaN2_lt_DDEN P q)]

theorem tilt_delta2_eq {P : Params2} {q : ℕ} (h : q ≤ P.X) :
    tilt (delta2 P) q = (DDEN : ℝ) / ((DDEN : ℝ) - deltaN2 P q) := nu2_eq h

/-- The per-prime factor of `T` (block form: `Q ≤ q`, same δ-value `dn` at `q`). -/
theorem tailFactor_le_fac2' {P : Params2} {q Q dn : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hqX : q ≤ P.X)
    (hdn : deltaN2 P q = dn) : tailFactor (delta2 P) q ≤ pv (fac2 Q dn) := by
  rw [pv_eq_div_ONE]
  refine tailFactor_le_fac2 hQ hQq (hdn ▸ deltaN2_lt_DDEN P q) (delta2_le_one P q) ?_
  rw [tilt_delta2_eq hqX, hdn]

theorem one_le_tailFactor2 (P : Params2) {q : ℕ} (hq : 1 ≤ q) : 1 ≤ tailFactor (delta2 P) q :=
  one_le_tailFactor (delta2_nonneg P q) (delta2_le_half P q) hq

theorem tailFactor2_nonneg (P : Params2) {q : ℕ} (hq : 1 ≤ q) : 0 ≤ tailFactor (delta2 P) q :=
  zero_le_one.trans (one_le_tailFactor2 P hq)

/-! ## The schedule beyond `PX` -/

theorem schedOk_spec {P : Params2} (h : schedOk P = true) :
    P.kps.size ≠ 0 ∧ P.kps[P.kps.size - 1]! ≤ P.PX ∧ P.PD ≤ P.PX := by
  unfold schedOk at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.2, h.2⟩

/-- With the run-time guard `schedOk` and `kps[0] ≤ PX`, the schedule is constant beyond `PX`. -/
theorem deltaN2_eq_of_gt {P : Params2} (hs : schedOk P = true) (h0 : P.kps[0]! ≤ P.PX) {p : ℕ}
    (hp : P.PX < p) : deltaN2 P p = min (P.kds[P.kds.size - 1]! * 1000) DNMAX2 := by
  obtain ⟨hsz, hlast, hPD⟩ := schedOk_spec hs
  unfold deltaN2
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), knotDelta6_of_ge hsz (by omega) (by omega)]

theorem deltaN2_const {P : Params2} (hs : schedOk P = true) (h0 : P.kps[0]! ≤ P.PX) {p q : ℕ}
    (hp : P.PX < p) (hq : P.PX < q) : deltaN2 P p = deltaN2 P q := by
  rw [deltaN2_eq_of_gt hs h0 hp, deltaN2_eq_of_gt hs h0 hq]

/-! ## `⌈m/p⌉` -/

theorem cdiv_le_two_iff {m p : ℕ} (hp : 0 < p) : cdiv m p ≤ 2 ↔ m ≤ 2 * p := by
  unfold cdiv
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hp]
  omega

/-! ## The array of primes -/

theorem primes2_toList (P : Params2) :
    (primes2 P).toList = MinModulus.CheckerSound.D.primeList (P.PX + 1) :=
  MinModulus.CheckerSound.A.primesUpTo_toList P.PX

theorem dns2_get! (P : Params2) {k : ℕ} (hk : k < (primes2 P).size) :
    (dns2 P)[k]! = deltaN2 P (primes2 P)[k]! :=
  MinModulus.CheckerSound.D.map_get! (primes2 P) (deltaN2 P) hk

theorem primes2_get!_prime (P : Params2) {k : ℕ} (hk : k < (primes2 P).size) :
    ((primes2 P)[k]!).Prime :=
  MinModulus.CheckerSound.D.get!_prime (primes2_toList P) hk

theorem primes2_get!_le (P : Params2) {k : ℕ} (hk : k < (primes2 P).size) :
    (primes2 P)[k]! ≤ P.PX := by
  have := MinModulus.CheckerSound.D.get!_lt (primes2_toList P) hk
  omega

end MinModulus.Checker2Sound.E
