import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Arith: from integer congruences to the product space, and the per-level inequality

STATUS: complete. No `sorry`; axioms are `propext`, `Classical.choice`, `Quot.sound` only.
Imports Mathlib only.

## Contents

* Weights (LEAN_DESIGN §4): `j0 p m d` (least `j ≥ 1` with `m ≤ d * p ^ j`),
  `w p m d = p ^ (1 - j0) / (p - 1)` (`zpow`), `U p m s = ∑ d ∈ s.divisors, w p m d`.
  Characterization for matching other definitions: `j0_spec`, `j0_le`, `j0_eq`, `w_eq_div`,
  `w_eq_inv_pow`. Geometric bound: `sum_inv_pow_le_w` (same shape as `Smooth.sum_le_wp`).
* (d) `hinge`: `max 0 (α - δ) / (1 - δ) ≤ max 0 (u - t) / (1 - t)` for `t ≤ δ < 1`, `α ≤ min 1 u`.
* (a) `Setup ι` (structure: `m`, `d`, `a`, `2 ≤ m`, `d` injective, `m ≤ d i`), and
  `Q = ∏ d i`, `n = #primeFactors Q`, `p : Fin n → ℕ` the increasing enumeration of the prime
  factors of `Q` (`p_strictMono`, `p_prime`, `image_p`), `γ j = Q.factorization (p j)`,
  `e i j = (d i).factorization (p j)`, `X j = ZMod (p j ^ γ j)` (an `abbrev`; `Fintype`,
  `DecidableEq`, `Nonempty` are found by instance search).
* (b) `toX : ℤ → ∀ j, X j` (`toX_surjective`, CRT). `side i j : Finset (X j)` = residues `≡ a i`
  mod `p j ^ e i j`; `C i = Fintype.piFinset (side i)`. Covering transfer
  `dvd_iff_toX_mem_C`; `exists_int_of_forall_not_mem_C`, `exists_int_of_forall_not_mem_B`.
* (c) `level i` = largest `j` with `p j ∣ d i` (`p_level_dvd`, `le_level`,
  `e_eq_zero_of_level_lt`, `one_le_e_level`); `B ℓ` = union of `C i` over `level i = ℓ`
  (`mem_B`, `B_eq_biUnion`); `B_congr` (= Distortion's `DependsLE S.B`); `alpha` (verbatim the
  Distortion definition); `alpha_le`; `card_side`.
* (e) `sum_le_U` (core, any `s ≠ 0`), `enlargement` (`V : Fin ℓ → ℕ`),
  `enlargement'` (`V : Fin n → ℕ`, product over `j < ℓ`). Abstract-weight versions
  `sum_le_sum_divisors`, `enlargement'_of_weight`, `enlargement_rect_of_weight` take any
  `W : ℕ → ℝ` with `∑_{k ∈ T} (p_ℓ⁻¹) ^ k ≤ W d` for admissible `T`; with `W := Smooth.wp (p ℓ) m`
  the hypothesis is `fun _ hd T hT => Smooth.sum_le_wp (S.p_prime ℓ).one_lt hd T hT` and the
  right side is `Smooth.Up` by definition. (Alternatively `U = Smooth.Up` for `1 < p`, via
  `j0_eq` and `w_eq_inv_pow`.)
* Comparison-ready forms: `wt`, `rect`, `rectExp`, `card_rect`, `rectExp_le_γ`,
  `alpha_le_rect`, `enlargement_rect`, `hinge_alpha_le`, `hinge_enlargement`.

## Changes relative to LEAN_DESIGN §5 (all strengthenings)

* `hinge` drops the unused hypotheses `0 ≤ t` and `0 ≤ α`.
* The enlargement lemmas drop the unused hypothesis `V j ≤ γ j`.
* `X j` is `ZMod (p j ^ γ j)` for the prime factors of `Q = ∏ d i` only (no other primes).
-/

open Finset

namespace MinModulus.Arith

/-! ## Weights `j0`, `w`, `U` (LEAN_DESIGN §4) -/

/-- `j0 p m d` is the least `j ≥ 1` with `m ≤ d * p ^ j` (junk value `0` if there is none;
there always is one when `2 ≤ p` and `1 ≤ d`, see `exists_j0`). -/
noncomputable def j0 (p m d : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, 1 ≤ j ∧ m ≤ d * p ^ j then Nat.find h else 0

/-- `w_p(d) = p ^ (1 - j0(d)) / (p - 1)`. -/
noncomputable def w (p m d : ℕ) : ℝ := (p : ℝ) ^ ((1 : ℤ) - (j0 p m d : ℤ)) / ((p : ℝ) - 1)

/-- `U_p(s) = ∑_{d ∣ s} w_p(d)`. -/
noncomputable def U (p m s : ℕ) : ℝ := ∑ d ∈ s.divisors, w p m d

theorem exists_j0 {p m d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) : ∃ j, 1 ≤ j ∧ m ≤ d * p ^ j := by
  refine ⟨m + 1, by omega, ?_⟩
  have h1 : m + 1 < p ^ (m + 1) := Nat.lt_pow_self (by omega)
  calc m ≤ p ^ (m + 1) := by omega
    _ ≤ d * p ^ (m + 1) := Nat.le_mul_of_pos_left _ (by omega)

theorem j0_spec {p m d : ℕ} (h : ∃ j, 1 ≤ j ∧ m ≤ d * p ^ j) :
    1 ≤ j0 p m d ∧ m ≤ d * p ^ j0 p m d := by
  unfold j0
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem j0_le {p m d j : ℕ} (hj : 1 ≤ j) (h : m ≤ d * p ^ j) : j0 p m d ≤ j := by
  have hex : ∃ j, 1 ≤ j ∧ m ≤ d * p ^ j := ⟨j, hj, h⟩
  unfold j0
  rw [dite_eq_left hex]
  exact Nat.find_min' hex ⟨hj, h⟩

/-- `j0` is characterized by: `1 ≤ k`, `m ≤ d * p ^ k`, and minimality. -/
theorem j0_eq {p m d k : ℕ} (hk1 : 1 ≤ k) (hk : m ≤ d * p ^ k)
    (hmin : ∀ j, 1 ≤ j → m ≤ d * p ^ j → k ≤ j) : j0 p m d = k :=
  le_antisymm (j0_le hk1 hk) (hmin _ (j0_spec ⟨k, hk1, hk⟩).1 (j0_spec ⟨k, hk1, hk⟩).2)

/-- `w` without `zpow`: `w_p(d) = p / (p ^ j0 * (p - 1))`. -/
theorem w_eq_div {p m d : ℕ} (hp : p ≠ 0) :
    w p m d = (p : ℝ) / ((p : ℝ) ^ j0 p m d * ((p : ℝ) - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  rw [w, zpow_sub₀ hp0, zpow_one, zpow_natCast, div_div]

/-- `w` in the form `(p⁻¹) ^ (j0 - 1) / (p - 1)` (valid when `1 ≤ j0`, e.g. under `exists_j0`). -/
theorem w_eq_inv_pow {p m d : ℕ} (hp : p ≠ 0) (hj : 1 ≤ j0 p m d) :
    w p m d = ((p : ℝ)⁻¹) ^ (j0 p m d - 1) / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  rw [w, inv_pow, ← zpow_natCast, ← zpow_neg, Nat.cast_sub hj, Nat.cast_one, neg_sub]

theorem w_nonneg {p m d : ℕ} (hp : 2 ≤ p) : 0 ≤ w p m d := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold w
  apply div_nonneg
  · exact zpow_nonneg (by linarith) _
  · linarith

/-- A finite set of admissible exponents `k` (i.e. `k ≥ 1`, `d * p ^ k ≥ m`) has
`∑ p ^ (-k) ≤ w_p(d) = ∑_{k ≥ j0} p ^ (-k)`. -/
theorem sum_inv_pow_le_w {p m d : ℕ} (hp : 2 ≤ p) (T : Finset ℕ)
    (hT : ∀ k ∈ T, 1 ≤ k ∧ m ≤ d * p ^ k) :
    ∑ k ∈ T, ((p : ℝ)⁻¹) ^ k ≤ w p m d := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨k0, hk0⟩
  · simpa using w_nonneg hp
  have hex : ∃ j, 1 ≤ j ∧ m ≤ d * p ^ j := ⟨k0, hT k0 hk0⟩
  set J := j0 p m d with hJdef
  have hJ : ∀ k ∈ T, J ≤ k := fun k hk => j0_le (hT k hk).1 (hT k hk).2
  set N := T.sup id + 1
  have hsub : T ⊆ Ico J N := fun k hk =>
    mem_Ico.2 ⟨hJ k hk, Nat.lt_succ_of_le (le_sup (f := id) hk)⟩
  have hp' : (1 : ℝ) < p := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hp0 : (0 : ℝ) < p := by linarith
  calc ∑ k ∈ T, ((p : ℝ)⁻¹) ^ k ≤ ∑ k ∈ Ico J N, ((p : ℝ)⁻¹) ^ k :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ((p : ℝ)⁻¹) ^ J / (1 - (p : ℝ)⁻¹) :=
        geom_sum_Ico_le_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp')
    _ = w p m d := by
        rw [w, ← hJdef, zpow_sub₀ hp0.ne', zpow_one, zpow_natCast, inv_pow]
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have h2 : (p : ℝ) ^ J ≠ 0 := pow_ne_zero _ hp0.ne'
        field_simp

/-- **Pointwise hinge step** (d). -/
theorem hinge {t δ α u : ℝ} (htδ : t ≤ δ) (hδ : δ < 1) (hα : α ≤ min 1 u) :
    max 0 (α - δ) / (1 - δ) ≤ max 0 (u - t) / (1 - t) := by
  have h1 : α ≤ 1 := hα.trans (min_le_left _ _)
  have h2 : α ≤ u := hα.trans (min_le_right _ _)
  have hδ' : 0 < 1 - δ := by linarith
  have ht' : 0 < 1 - t := by linarith
  rcases le_or_gt α δ with h | h
  · rw [max_eq_left (by linarith), zero_div]
    exact div_nonneg (le_max_left _ _) ht'.le
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), div_le_div_iff₀ hδ' ht']
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 htδ), mul_nonneg (sub_nonneg.2 h2) hδ'.le]

/-! ## Setup -/

/-- The data of a system of congruences `a i (mod d i)` with distinct moduli `d i ≥ m ≥ 2`. -/
structure Setup (ι : Type*) where
  m : ℕ
  d : ι → ℕ
  a : ι → ℤ
  two_le_m : 2 ≤ m
  d_injective : Function.Injective d
  m_le_d : ∀ i, m ≤ d i

namespace Setup

variable {ι : Type*} [Fintype ι] (S : Setup ι)

/-- `Q = ∏ d_i`. -/
def Q : ℕ := ∏ i, S.d i

/-- The number of prime factors of `Q`. -/
def n : ℕ := S.Q.primeFactors.card

/-- The prime factors `p_0 < p_1 < ⋯ < p_{n-1}` of `Q`. -/
def p (j : Fin S.n) : ℕ := S.Q.primeFactors.orderEmbOfFin rfl j

/-- `γ_j = v_{p_j}(Q)`. -/
def γ (j : Fin S.n) : ℕ := S.Q.factorization (S.p j)

/-- `e_{ij} = v_{p_j}(d_i)`. -/
def e (i : ι) (j : Fin S.n) : ℕ := (S.d i).factorization (S.p j)

/-- The coordinate spaces `X_j = ℤ / p_j ^ γ_j`. -/
abbrev X (j : Fin S.n) : Type := ZMod (S.p j ^ S.γ j)

omit [Fintype ι] in
theorem d_pos (i : ι) : 0 < S.d i := by
  have := S.m_le_d i
  have := S.two_le_m
  omega

omit [Fintype ι] in
theorem d_ne_zero (i : ι) : S.d i ≠ 0 := (S.d_pos i).ne'

theorem Q_ne_zero : S.Q ≠ 0 := prod_ne_zero_iff.2 fun i _ => S.d_ne_zero i

theorem d_dvd_Q (i : ι) : S.d i ∣ S.Q := dvd_prod_of_mem _ (mem_univ i)

theorem p_mem (j : Fin S.n) : S.p j ∈ S.Q.primeFactors := orderEmbOfFin_mem _ _ _

theorem p_prime (j : Fin S.n) : (S.p j).Prime := Nat.prime_of_mem_primeFactors (S.p_mem j)

theorem p_strictMono : StrictMono S.p := (S.Q.primeFactors.orderEmbOfFin rfl).strictMono

theorem p_injective : Function.Injective S.p := S.p_strictMono.injective

theorem p_lt_p_iff {j k : Fin S.n} : S.p j < S.p k ↔ j < k := S.p_strictMono.lt_iff_lt

theorem image_p : univ.image S.p = S.Q.primeFactors := image_orderEmbOfFin_univ _ _

theorem exists_p_eq {q : ℕ} (hq : q ∈ S.Q.primeFactors) : ∃ j, S.p j = q := by
  rw [← S.image_p, mem_image] at hq
  obtain ⟨j, -, hj⟩ := hq
  exact ⟨j, hj⟩

/-- The primes `p_j` with `j < ℓ` are exactly the prime factors of `Q` below `p_ℓ`. -/
theorem image_p_filter_lt (ℓ : Fin S.n) :
    (univ.filter (· < ℓ)).image S.p = S.Q.primeFactors.filter (· < S.p ℓ) := by
  ext q
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨S.p_mem j, S.p_lt_p_iff.2 hj⟩
  · rintro ⟨hq, hlt⟩
    obtain ⟨j, rfl⟩ := S.exists_p_eq hq
    exact ⟨j, S.p_lt_p_iff.1 hlt, rfl⟩

instance neZero_p (j : Fin S.n) : NeZero (S.p j) := ⟨(S.p_prime j).ne_zero⟩

example (j : Fin S.n) : Fintype (S.X j) := inferInstance
example (j : Fin S.n) : Nonempty (S.X j) := inferInstance
example (j : Fin S.n) : DecidableEq (S.X j) := inferInstance

theorem card_X (j : Fin S.n) : Fintype.card (S.X j) = S.p j ^ S.γ j := ZMod.card _

theorem e_le_γ (i : ι) (j : Fin S.n) : S.e i j ≤ S.γ j :=
  (Nat.factorization_le_iff_dvd (S.d_ne_zero i) S.Q_ne_zero).2 (S.d_dvd_Q i) (S.p j)

theorem coprime_p_pow {j k : Fin S.n} (hjk : j ≠ k) (a b : ℕ) :
    Nat.Coprime (S.p j ^ a) (S.p k ^ b) :=
  Nat.Coprime.pow _ _ ((Nat.coprime_primes (S.p_prime j) (S.p_prime k)).2 (S.p_injective.ne hjk))

/-- Every divisor of `Q` is the product of its `p_j`-parts. -/
theorem eq_prod_of_dvd_Q {k : ℕ} (hk : k ∣ S.Q) : k = ∏ j, S.p j ^ k.factorization (S.p j) := by
  have hk0 : k ≠ 0 := fun h => S.Q_ne_zero (zero_dvd_iff.1 (h ▸ hk))
  have hsub : k.primeFactors ⊆ S.Q.primeFactors := Nat.primeFactors_mono hk S.Q_ne_zero
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hk0]
  rw [prod_subset hsub (fun q _ hq => by
      rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization]), pow_zero]),
    ← S.image_p, prod_image S.p_injective.injOn]

theorem d_eq_prod (i : ι) : S.d i = ∏ j, S.p j ^ S.e i j := S.eq_prod_of_dvd_Q (S.d_dvd_Q i)

/-- Divisibility by a divisor `k` of `Q` is checked prime by prime. -/
theorem natCast_dvd_of_forall {k : ℕ} (hk : k ∣ S.Q) {z : ℤ}
    (h : ∀ j, ((S.p j ^ k.factorization (S.p j) : ℕ) : ℤ) ∣ z) : (k : ℤ) ∣ z := by
  rw [S.eq_prod_of_dvd_Q hk, Nat.cast_prod]
  refine Fintype.prod_dvd_of_coprime (fun j j' hjj' => ?_) h
  exact Nat.isCoprime_iff_coprime.2 (S.coprime_p_pow hjj' _ _)

/-! ### The CRT map -/

/-- The reduction map `ℤ → ∏_j ℤ / p_j ^ γ_j`. -/
def toX (x : ℤ) : ∀ j, S.X j := fun j => (x : ZMod (S.p j ^ S.γ j))

/-- **CRT**: the reduction map is surjective. -/
theorem toX_surjective : Function.Surjective S.toX := by
  intro y
  have hcop : Pairwise (Function.onFun Nat.Coprime fun j => S.p j ^ S.γ j) := fun j k hjk =>
    S.coprime_p_pow hjk _ _
  let φ := ZMod.prodEquivPi (fun j => S.p j ^ S.γ j) hcop
  obtain ⟨x, hx⟩ := ZMod.intCast_surjective (φ.symm y)
  refine ⟨x, ?_⟩
  have h : S.toX x = φ (x : ZMod _) := by
    funext j
    simp [toX, φ, ZMod.prodEquivPi_apply, map_intCast]
  rw [h, hx, RingEquiv.apply_symm_apply]

/-! ### Sides and cylinders -/

/-- The side of the cylinder `C_i` in `X_j`: residues `z` with `z ≡ a_i (mod p_j ^ e_{ij})`. -/
def side (i : ι) (j : Fin S.n) : Finset (S.X j) :=
  univ.filter fun z =>
    ZMod.castHom (pow_dvd_pow (S.p j) (S.e_le_γ i j)) (ZMod (S.p j ^ S.e i j)) z =
      ((S.a i : ℤ) : ZMod (S.p j ^ S.e i j))

/-- The cylinder `C_i = ∏_j side i j`, the image of the progression `a_i (mod d_i)`. -/
def C (i : ι) : Finset (∀ j, S.X j) := Fintype.piFinset (S.side i)

theorem mem_C {i : ι} {y : ∀ j, S.X j} : y ∈ S.C i ↔ ∀ j, y j ∈ S.side i j :=
  Fintype.mem_piFinset

/-- The sides have `p_j ^ (γ_j - e_{ij})` elements. -/
theorem card_side (i : ι) (j : Fin S.n) : (S.side i j).card = S.p j ^ (S.γ j - S.e i j) := by
  classical
  set f := ZMod.castHom (pow_dvd_pow (S.p j) (S.e_le_γ i j)) (ZMod (S.p j ^ S.e i j))
  have hsurj := ZMod.castHom_surjective (pow_dvd_pow (S.p j) (S.e_le_γ i j))
  have hall : ∀ c : ZMod (S.p j ^ S.e i j),
      (univ.filter fun z : S.X j => f z = c).card = (S.side i j).card := fun c =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hsurj c) (hsurj _)
  have htot := card_eq_sum_card_fiberwise (s := (univ : Finset (S.X j)))
    (t := (univ : Finset (ZMod (S.p j ^ S.e i j)))) (f := f) (fun _ _ => mem_coe.2 (mem_univ _))
  rw [sum_congr rfl (fun c _ => hall c), sum_const, card_univ, card_univ, ZMod.card, ZMod.card,
    smul_eq_mul, ← Nat.pow_sub_mul_pow (S.p j) (S.e_le_γ i j), mul_comm] at htot
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (S.p_prime j).pos _) htot).symm

theorem toX_mem_side (x : ℤ) (i : ι) (j : Fin S.n) :
    S.toX x j ∈ S.side i j ↔ ((S.p j ^ S.e i j : ℕ) : ℤ) ∣ x - S.a i := by
  simp only [side, mem_filter, mem_univ, true_and, toX, map_intCast]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, dvd_sub_comm]

theorem side_eq_univ_of_e_eq_zero {i : ι} {j : Fin S.n} (h : S.e i j = 0) : S.side i j = univ := by
  ext z
  simp only [side, mem_filter, mem_univ, true_and, iff_true]
  have : Subsingleton (ZMod (S.p j ^ S.e i j)) := ZMod.subsingleton_iff.2 (by rw [h, pow_zero])
  exact Subsingleton.elim _ _

/-- **Covering transfer**: `d_i ∣ x - a_i` iff the image of `x` lies in `C_i`. -/
theorem dvd_iff_toX_mem_C (i : ι) (x : ℤ) : (S.d i : ℤ) ∣ x - S.a i ↔ S.toX x ∈ S.C i := by
  rw [mem_C]
  simp_rw [toX_mem_side]
  constructor
  · intro h j
    exact (Int.natCast_dvd_natCast.2 (Nat.ordProj_dvd _ _)).trans h
  · exact S.natCast_dvd_of_forall (S.d_dvd_Q i)

/-- A point outside every cylinder yields an integer covered by no congruence. -/
theorem exists_int_of_forall_not_mem_C (y : ∀ j, S.X j) (hy : ∀ i, y ∉ S.C i) :
    ∃ x : ℤ, ∀ i, ¬ (S.d i : ℤ) ∣ x - S.a i := by
  obtain ⟨x, rfl⟩ := S.toX_surjective y
  exact ⟨x, fun i h => hy i ((S.dvd_iff_toX_mem_C i x).1 h)⟩

/-! ### Levels -/

theorem exists_p_dvd (i : ι) : ∃ j, S.p j ∣ S.d i := by
  have h1 : S.d i ≠ 1 := by
    have := S.m_le_d i
    have := S.two_le_m
    omega
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd h1
  obtain ⟨j, hj⟩ := S.exists_p_eq (Nat.mem_primeFactors.2 ⟨hq, hqd.trans (S.d_dvd_Q i), S.Q_ne_zero⟩)
  exact ⟨j, hj ▸ hqd⟩

/-- `level i` is the largest `j` with `p_j ∣ d_i` (the index of the largest prime of `d_i`). -/
def level (i : ι) : Fin S.n :=
  (univ.filter fun j => S.p j ∣ S.d i).max' (by
    obtain ⟨j, hj⟩ := S.exists_p_dvd i
    exact ⟨j, mem_filter.2 ⟨mem_univ _, hj⟩⟩)

theorem p_level_dvd (i : ι) : S.p (S.level i) ∣ S.d i :=
  (mem_filter.1 (max'_mem (univ.filter fun j => S.p j ∣ S.d i) _)).2

theorem le_level {i : ι} {j : Fin S.n} (h : S.p j ∣ S.d i) : j ≤ S.level i :=
  le_max' (univ.filter fun j => S.p j ∣ S.d i) j (mem_filter.2 ⟨mem_univ _, h⟩)

theorem e_eq_zero_of_level_lt {i : ι} {j : Fin S.n} (h : S.level i < j) : S.e i j = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun hd => absurd (S.le_level hd) (not_le.2 h)

theorem one_le_e_level (i : ι) : 1 ≤ S.e i (S.level i) :=
  (S.p_prime _).factorization_pos_of_dvd (S.d_ne_zero i) (S.p_level_dvd i)

/-- `B ℓ` is the union of the cylinders `C_i` with `level i = ℓ`. -/
def B (ℓ : Fin S.n) : Finset (∀ j, S.X j) := univ.filter fun y => ∃ i, S.level i = ℓ ∧ y ∈ S.C i

theorem mem_B {ℓ : Fin S.n} {y : ∀ j, S.X j} : y ∈ S.B ℓ ↔ ∃ i, S.level i = ℓ ∧ y ∈ S.C i := by
  simp [B]

theorem B_eq_biUnion (ℓ : Fin S.n) :
    S.B ℓ = (univ.filter fun i => S.level i = ℓ).biUnion S.C := by
  ext y
  simp only [mem_B, mem_biUnion, mem_filter, mem_univ, true_and]

theorem C_subset_B (i : ι) : S.C i ⊆ S.B (S.level i) := fun _ hy => S.mem_B.2 ⟨i, rfl, hy⟩

/-- A point outside every `B ℓ` yields an integer covered by no congruence. -/
theorem exists_int_of_forall_not_mem_B (y : ∀ j, S.X j) (hy : ∀ ℓ, y ∉ S.B ℓ) :
    ∃ x : ℤ, ∀ i, ¬ (S.d i : ℤ) ∣ x - S.a i :=
  S.exists_int_of_forall_not_mem_C y fun i hi => hy _ (S.C_subset_B i hi)

/-- `B ℓ` depends only on the coordinates `≤ ℓ` (this is Distortion's `DependsLE S.B`). -/
theorem B_congr (ℓ : Fin S.n) (y y' : ∀ j, S.X j) (h : ∀ j, j ≤ ℓ → y j = y' j) :
    y ∈ S.B ℓ ↔ y' ∈ S.B ℓ := by
  suffices key : ∀ y y' : ∀ j, S.X j, (∀ j, j ≤ ℓ → y j = y' j) → y ∈ S.B ℓ → y' ∈ S.B ℓ from
    ⟨key y y' h, key y' y fun j hj => (h j hj).symm⟩
  intro y y' h hy
  obtain ⟨i, hi, hyi⟩ := S.mem_B.1 hy
  refine S.mem_B.2 ⟨i, hi, S.mem_C.2 fun j => ?_⟩
  rcases le_or_gt j ℓ with hj | hj
  · rw [← h j hj]
    exact S.mem_C.1 hyi j
  · rw [S.side_eq_univ_of_e_eq_zero (S.e_eq_zero_of_level_lt (hi ▸ hj))]
    exact mem_univ _

/-! ### Fibre coverage -/

/-- The fibre coverage `α ℓ x = #{y ∈ X ℓ | update x ℓ y ∈ B ℓ} / #X ℓ` (as in Distortion). -/
noncomputable def alpha (ℓ : Fin S.n) (x : ∀ j, S.X j) : ℝ :=
  ((univ.filter fun y : S.X ℓ => Function.update x ℓ y ∈ S.B ℓ).card : ℝ) /
    (Fintype.card (S.X ℓ) : ℝ)

theorem alpha_congr (ℓ : Fin S.n) (x x' : ∀ j, S.X j) (h : ∀ j, j < ℓ → x j = x' j) :
    S.alpha ℓ x = S.alpha ℓ x' := by
  unfold alpha
  congr 3
  ext y
  simp only [mem_filter, mem_univ, true_and]
  refine S.B_congr ℓ _ _ fun j hj => ?_
  rcases hj.lt_or_eq with hj | rfl
  · rw [Function.update_of_ne hj.ne, Function.update_of_ne hj.ne]
    exact h j hj
  · rw [Function.update_self, Function.update_self]

theorem card_side_div (i : ι) (j : Fin S.n) :
    ((S.side i j).card : ℝ) / (Fintype.card (S.X j) : ℝ) = ((S.p j : ℝ) ^ S.e i j)⁻¹ := by
  have hp0 : (0 : ℝ) < S.p j := by exact_mod_cast (S.p_prime j).pos
  rw [card_side, card_X, ← Nat.pow_sub_mul_pow (S.p j) (S.e_le_γ i j)]
  push_cast
  have h1 : (S.p j : ℝ) ^ (S.γ j - S.e i j) ≠ 0 := pow_ne_zero _ hp0.ne'
  have h2 : (S.p j : ℝ) ^ S.e i j ≠ 0 := pow_ne_zero _ hp0.ne'
  field_simp

/-- **Fibre union bound** (c): `α ℓ x ≤ min 1 (∑_{level i = ℓ} p_ℓ ^ (-e_{iℓ}) [x_{<ℓ} ∈ A'_i])`. -/
theorem alpha_le (ℓ : Fin S.n) (x : ∀ j, S.X j) :
    S.alpha ℓ x ≤ min 1 (∑ i ∈ univ.filter (fun i => S.level i = ℓ),
      ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ * (if ∀ j, j < ℓ → x j ∈ S.side i j then 1 else 0)) := by
  classical
  have hN : (0 : ℝ) < Fintype.card (S.X ℓ) := by exact_mod_cast Fintype.card_pos
  apply le_min
  · rw [alpha, div_le_one hN]
    exact_mod_cast card_le_univ _
  · set I := univ.filter (fun i => S.level i = ℓ ∧ ∀ j, j < ℓ → x j ∈ S.side i j) with hI
    have hsub : (univ.filter fun y : S.X ℓ => Function.update x ℓ y ∈ S.B ℓ) ⊆
        I.biUnion (fun i => S.side i ℓ) := by
      intro y hy
      obtain ⟨i, hi, hyC⟩ := S.mem_B.1 (mem_filter.1 hy).2
      rw [mem_C] at hyC
      refine mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, hi, fun j hj => ?_⟩, ?_⟩
      · have := hyC j
        rwa [Function.update_of_ne hj.ne] at this
      · have := hyC ℓ
        rwa [Function.update_self] at this
    have hcard := (card_le_card hsub).trans card_biUnion_le
    calc S.alpha ℓ x ≤ (∑ i ∈ I, ((S.side i ℓ).card : ℝ)) / Fintype.card (S.X ℓ) := by
          rw [alpha]
          gcongr
          exact_mod_cast hcard
      _ = ∑ i ∈ I, ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ := by
          rw [sum_div]
          exact sum_congr rfl fun i _ => S.card_side_div i ℓ
      _ = _ := by
          rw [hI, ← filter_filter, sum_filter (fun i => ∀ j, j < ℓ → x j ∈ S.side i j)]
          refine sum_congr rfl fun i _ => ?_
          split_ifs <;> simp

/-! ### Enlargement -/

/-- For `level i = ℓ`: `d_i / p_ℓ ^ e_{iℓ} ∣ s` as soon as `p_j ^ e_{ij} ∣ s` for all `j < ℓ`. -/
theorem ordCompl_dvd_of {i : ι} {ℓ : Fin S.n} (hi : S.level i = ℓ) {s : ℕ}
    (h : ∀ j, j < ℓ → S.p j ^ S.e i j ∣ s) : S.d i / S.p ℓ ^ S.e i ℓ ∣ s := by
  have hk : S.d i / S.p ℓ ^ S.e i ℓ ∣ S.Q := (Nat.div_dvd_of_dvd (Nat.ordProj_dvd _ _)).trans (S.d_dvd_Q i)
  refine Int.natCast_dvd_natCast.1 (S.natCast_dvd_of_forall hk fun j => ?_)
  rw [e, Nat.factorization_ordCompl]
  rcases lt_trichotomy j ℓ with hj | rfl | hj
  · rw [Finsupp.erase_ne (S.p_injective.ne hj.ne)]
    exact Int.natCast_dvd_natCast.2 (h j hj)
  · rw [Finsupp.erase_same, pow_zero, Nat.cast_one]
    exact one_dvd _
  · rw [Finsupp.erase_ne (S.p_injective.ne hj.ne')]
    have : (S.d i).factorization (S.p j) = 0 := S.e_eq_zero_of_level_lt (hi ▸ hj)
    rw [this, pow_zero, Nat.cast_one]
    exact one_dvd _

/-- **Enlargement, core form with an abstract weight** (uses `d` injective and `d_i ≥ m`).
Let `W : ℕ → ℝ` dominate `∑_{k ∈ T} p_ℓ ^ (-k)` for every `d ≥ 1` and every finite set `T` of
admissible exponents (`k ≥ 1`, `d * p_ℓ ^ k ≥ m`). Then for every `s ≠ 0`,
`∑_{level i = ℓ} p_ℓ ^ (-e_{iℓ}) [d_i / p_ℓ ^ e_{iℓ} ∣ s] ≤ ∑_{d ∣ s} W d`.
(For `W = w (p ℓ) m` see `sum_le_U`; `Smooth.sum_le_wp` gives the hypothesis for `Smooth.wp`.) -/
theorem sum_le_sum_divisors (ℓ : Fin S.n) {s : ℕ} (hs : s ≠ 0) (W : ℕ → ℝ)
    (hW : ∀ d, 0 < d → ∀ T : Finset ℕ, (∀ k ∈ T, 1 ≤ k ∧ S.m ≤ d * S.p ℓ ^ k) →
      ∑ k ∈ T, ((S.p ℓ : ℝ)⁻¹) ^ k ≤ W d) :
    ∑ i ∈ univ.filter (fun i => S.level i = ℓ),
      ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ * (if S.d i / S.p ℓ ^ S.e i ℓ ∣ s then 1 else 0)
      ≤ ∑ d ∈ s.divisors, W d := by
  classical
  set I := univ.filter (fun i => S.level i = ℓ ∧ S.d i / S.p ℓ ^ S.e i ℓ ∣ s) with hI
  have hL : ∑ i ∈ univ.filter (fun i => S.level i = ℓ),
      ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ * (if S.d i / S.p ℓ ^ S.e i ℓ ∣ s then 1 else 0)
      = ∑ i ∈ I, ((S.p ℓ : ℝ)⁻¹) ^ S.e i ℓ := by
    rw [hI, ← filter_filter, sum_filter (fun i => S.d i / S.p ℓ ^ S.e i ℓ ∣ s)]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [inv_pow]
  rw [hL]
  have hmaps : ∀ i ∈ I, S.d i / S.p ℓ ^ S.e i ℓ ∈ s.divisors := fun i hi =>
    Nat.mem_divisors.2 ⟨(mem_filter.1 hi).2.2, hs⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun k hk => ?_
  -- the fibre over `k`: `i ↦ e i ℓ` is injective on it, since `d i = p_ℓ ^ (e i ℓ) * k`
  have hdecomp : ∀ i, S.p ℓ ^ S.e i ℓ * (S.d i / S.p ℓ ^ S.e i ℓ) = S.d i := fun i =>
    Nat.ordProj_mul_ordCompl_eq_self _ _
  have hinj : Set.InjOn (fun i => S.e i ℓ)
      ↑(I.filter fun i => S.d i / S.p ℓ ^ S.e i ℓ = k) := by
    intro i hi i' hi' hii'
    have hi := (mem_filter.1 (mem_coe.1 hi)).2
    have hi' := (mem_filter.1 (mem_coe.1 hi')).2
    simp only at hii'
    apply S.d_injective
    rw [← hdecomp i, ← hdecomp i', hi, hi', hii']
  rw [← sum_image (f := fun e' => ((S.p ℓ : ℝ)⁻¹) ^ e') hinj]
  refine hW k (Nat.pos_of_mem_divisors hk) _ fun e' he' => ?_
  obtain ⟨i, hi, rfl⟩ := mem_image.1 he'
  obtain ⟨hiI, hik⟩ := mem_filter.1 hi
  have hlev : S.level i = ℓ := (mem_filter.1 hiI).2.1
  refine ⟨hlev ▸ S.one_le_e_level i, ?_⟩
  rw [← hik, mul_comm, hdecomp i]
  exact S.m_le_d i

/-- **Enlargement, core form**: for every `s ≠ 0`,
`∑_{level i = ℓ} p_ℓ ^ (-e_{iℓ}) [d_i / p_ℓ ^ e_{iℓ} ∣ s] ≤ U_{p_ℓ}(s)`. -/
theorem sum_le_U (ℓ : Fin S.n) {s : ℕ} (hs : s ≠ 0) :
    ∑ i ∈ univ.filter (fun i => S.level i = ℓ),
      ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ * (if S.d i / S.p ℓ ^ S.e i ℓ ∣ s then 1 else 0)
      ≤ U (S.p ℓ) S.m s :=
  S.sum_le_sum_divisors ℓ hs (w (S.p ℓ) S.m) fun _ _ T hT =>
    sum_inv_pow_le_w (S.p_prime ℓ).two_le T hT

/-- **Enlargement**, with `V : Fin ℓ → ℕ` (the exponents of `p_0, …, p_{ℓ-1}`). -/
theorem enlargement (ℓ : Fin S.n) (V : Fin ℓ → ℕ) :
    ∑ i ∈ univ.filter (fun i => S.level i = ℓ),
      ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ *
        (if ∀ j : Fin ℓ, S.e i (Fin.castLE ℓ.isLt.le j) ≤ V j then 1 else 0)
      ≤ U (S.p ℓ) S.m (∏ j : Fin ℓ, S.p (Fin.castLE ℓ.isLt.le j) ^ V j) := by
  have hs : ∏ j : Fin ℓ, S.p (Fin.castLE ℓ.isLt.le j) ^ V j ≠ 0 :=
    prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (S.p_prime _).ne_zero
  refine le_trans (sum_le_sum fun i hi => ?_) (S.sum_le_U ℓ hs)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  split_ifs with hA hB
  · exact le_rfl
  · exfalso
    refine hB (S.ordCompl_dvd_of (mem_filter.1 hi).2 fun j hj => ?_)
    have hj' : Fin.castLE ℓ.isLt.le (⟨j, hj⟩ : Fin ℓ) = j := Fin.ext rfl
    have hle := hA ⟨j, hj⟩
    have hmem := dvd_prod_of_mem (fun k : Fin ℓ => S.p (Fin.castLE ℓ.isLt.le k) ^ V k)
      (mem_univ (⟨j, hj⟩ : Fin ℓ))
    simp only [hj'] at hle hmem
    exact (pow_dvd_pow _ hle).trans hmem
  · exact zero_le_one
  · exact le_rfl

/-- **Enlargement**, abstract weight, with `V : Fin n → ℕ` and the product over `j < ℓ`. -/
theorem enlargement'_of_weight (ℓ : Fin S.n) (V : Fin S.n → ℕ) (W : ℕ → ℝ)
    (hW : ∀ d, 0 < d → ∀ T : Finset ℕ, (∀ k ∈ T, 1 ≤ k ∧ S.m ≤ d * S.p ℓ ^ k) →
      ∑ k ∈ T, ((S.p ℓ : ℝ)⁻¹) ^ k ≤ W d) :
    ∑ i ∈ univ.filter (fun i => S.level i = ℓ),
      ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ * (if ∀ j, j < ℓ → S.e i j ≤ V j then 1 else 0)
      ≤ ∑ d ∈ (∏ j ∈ univ.filter (· < ℓ), S.p j ^ V j).divisors, W d := by
  have hs : ∏ j ∈ univ.filter (· < ℓ), S.p j ^ V j ≠ 0 :=
    prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (S.p_prime _).ne_zero
  refine le_trans (sum_le_sum fun i hi => ?_) (S.sum_le_sum_divisors ℓ hs W hW)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  split_ifs with hA hB
  · exact le_rfl
  · exfalso
    exact hB (S.ordCompl_dvd_of (mem_filter.1 hi).2 fun j hj =>
      (pow_dvd_pow _ (hA j hj)).trans (dvd_prod_of_mem _ (mem_filter.2 ⟨mem_univ _, hj⟩)))
  · exact zero_le_one
  · exact le_rfl

/-- **Enlargement**, with `V : Fin n → ℕ` and the product over the coordinates `j < ℓ`. -/
theorem enlargement' (ℓ : Fin S.n) (V : Fin S.n → ℕ) :
    ∑ i ∈ univ.filter (fun i => S.level i = ℓ),
      ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ * (if ∀ j, j < ℓ → S.e i j ≤ V j then 1 else 0)
      ≤ U (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ V j) :=
  S.enlargement'_of_weight ℓ V (w (S.p ℓ) S.m) fun _ _ T hT =>
    sum_inv_pow_le_w (S.p_prime ℓ).two_le T hT

/-! ### Comparison-ready forms

Index set `ι` (all congruences), with weights vanishing off level `ℓ`, and the cylinder `A'_i`
written as a rectangle on the full space (`univ` in the coordinates `≥ ℓ`). -/

/-- Weight of congruence `i` at level `ℓ`: `p_ℓ ^ (-e_{iℓ})` if `level i = ℓ`, else `0`. -/
noncomputable def wt (ℓ : Fin S.n) (i : ι) : ℝ :=
  if S.level i = ℓ then ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ else 0

theorem wt_nonneg (ℓ : Fin S.n) (i : ι) : 0 ≤ S.wt ℓ i := by
  unfold wt
  split_ifs <;> positivity

/-- The rectangle of `A'_i` at level `ℓ`: side `side i j` for `j < ℓ`, and `univ` for `j ≥ ℓ`. -/
def rect (ℓ : Fin S.n) (i : ι) (j : Fin S.n) : Finset (S.X j) :=
  if j < ℓ then S.side i j else univ

/-- The exponent of the side of `rect ℓ i` at `j`: `e_{ij}` for `j < ℓ`, `0` for `j ≥ ℓ`. -/
def rectExp (ℓ : Fin S.n) (i : ι) (j : Fin S.n) : ℕ := if j < ℓ then S.e i j else 0

theorem rectExp_le_γ (ℓ : Fin S.n) (i : ι) (j : Fin S.n) : S.rectExp ℓ i j ≤ S.γ j := by
  unfold rectExp
  split_ifs
  · exact S.e_le_γ i j
  · exact Nat.zero_le _

theorem card_rect (ℓ : Fin S.n) (i : ι) (j : Fin S.n) :
    (S.rect ℓ i j).card = S.p j ^ (S.γ j - S.rectExp ℓ i j) := by
  unfold rect rectExp
  split_ifs
  · exact S.card_side i j
  · rw [card_univ, card_X, Nat.sub_zero]

theorem forall_mem_rect_iff (ℓ : Fin S.n) (i : ι) (x : ∀ j, S.X j) :
    (∀ j, x j ∈ S.rect ℓ i j) ↔ ∀ j, j < ℓ → x j ∈ S.side i j := by
  unfold rect
  constructor
  · intro h j hj
    have := h j
    rwa [ite_eq_left hj] at this
  · intro h j
    split_ifs with hj
    · exact h j hj
    · exact mem_univ _

theorem forall_rectExp_le_iff (ℓ : Fin S.n) (i : ι) (V : Fin S.n → ℕ) :
    (∀ j, S.rectExp ℓ i j ≤ V j) ↔ ∀ j, j < ℓ → S.e i j ≤ V j := by
  unfold rectExp
  constructor
  · intro h j hj
    have := h j
    rwa [ite_eq_left hj] at this
  · intro h j
    split_ifs with hj
    · exact h j hj
    · exact Nat.zero_le _

theorem sum_filter_level_eq (ℓ : Fin S.n) (A : ι → Prop) [DecidablePred A] :
    ∑ i ∈ univ.filter (fun i => S.level i = ℓ), ((S.p ℓ : ℝ) ^ S.e i ℓ)⁻¹ * (if A i then 1 else 0)
      = ∑ i, (if A i then S.wt ℓ i else 0) := by
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  unfold wt
  split_ifs <;> simp

/-- `alpha_le` in the form used by the comparison theorem. -/
theorem alpha_le_rect (ℓ : Fin S.n) (x : ∀ j, S.X j) :
    S.alpha ℓ x ≤ min 1 (∑ i, (if ∀ j, x j ∈ S.rect ℓ i j then S.wt ℓ i else 0)) := by
  refine (S.alpha_le ℓ x).trans (le_of_eq ?_)
  rw [S.sum_filter_level_eq ℓ]
  exact congrArg _ (sum_congr rfl fun i _ => if_congr (S.forall_mem_rect_iff ℓ i x).symm rfl rfl)

/-- Enlargement in the form produced by the `V`-law of the comparison theorem, abstract weight. -/
theorem enlargement_rect_of_weight (ℓ : Fin S.n) (V : Fin S.n → ℕ) (W : ℕ → ℝ)
    (hW : ∀ d, 0 < d → ∀ T : Finset ℕ, (∀ k ∈ T, 1 ≤ k ∧ S.m ≤ d * S.p ℓ ^ k) →
      ∑ k ∈ T, ((S.p ℓ : ℝ)⁻¹) ^ k ≤ W d) :
    ∑ i, (if ∀ j, S.rectExp ℓ i j ≤ V j then S.wt ℓ i else 0)
      ≤ ∑ d ∈ (∏ j ∈ univ.filter (· < ℓ), S.p j ^ V j).divisors, W d := by
  refine le_of_eq_of_le ?_ (S.enlargement'_of_weight ℓ V W hW)
  rw [S.sum_filter_level_eq ℓ]
  exact sum_congr rfl fun i _ => if_congr (S.forall_rectExp_le_iff ℓ i V) rfl rfl

/-- Enlargement in the form produced by the `V`-law of the comparison theorem. -/
theorem enlargement_rect (ℓ : Fin S.n) (V : Fin S.n → ℕ) :
    ∑ i, (if ∀ j, S.rectExp ℓ i j ≤ V j then S.wt ℓ i else 0)
      ≤ U (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ V j) :=
  S.enlargement_rect_of_weight ℓ V (w (S.p ℓ) S.m) fun _ _ T hT =>
    sum_inv_pow_le_w (S.p_prime ℓ).two_le T hT

/-- Pointwise step on the product space: (c) followed by (d). -/
theorem hinge_alpha_le (ℓ : Fin S.n) (x : ∀ j, S.X j) {t δ : ℝ} (htδ : t ≤ δ) (hδ : δ < 1) :
    max 0 (S.alpha ℓ x - δ) / (1 - δ) ≤
      max 0 (∑ i, (if ∀ j, x j ∈ S.rect ℓ i j then S.wt ℓ i else 0) - t) / (1 - t) :=
  hinge htδ hδ (S.alpha_le_rect ℓ x)

/-- Pointwise step on the aligned side: the hinge is monotone, so (e) passes through it. -/
theorem hinge_enlargement (ℓ : Fin S.n) (V : Fin S.n → ℕ) (t : ℝ) :
    max 0 (∑ i, (if ∀ j, S.rectExp ℓ i j ≤ V j then S.wt ℓ i else 0) - t) ≤
      max 0 (U (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ V j) - t) :=
  max_le_max le_rfl (sub_le_sub_right (S.enlargement_rect ℓ V) t)

end Setup

end MinModulus.Arith
