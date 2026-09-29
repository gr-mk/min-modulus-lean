import MinModulus.Smooth.Main
import MinModulus.Main.Certificate
import Mathlib.Data.Finset.NatDivisors

/-!
# `Checker2Math.Identities`: the exact identities behind the second checker

STATUS: complete, no `sorry` (lean2 stage 1). Every theorem depends only on `propext`,
`Classical.choice`, `Quot.sound` (checked with `#print axioms`). Owned by the lean2 lead; stage-2
math (the laws `lawJoint`, `lawE`, the DFS and suffix bounds) goes into new files (see
`SCRATCH/agents/lean2/LEAN2_DESIGN.md` §6).

Notation (`Smooth`): `U_p(s) = Σ_{d ∣ s} w_p(d)`, `w_p(d) = p^{1 − j0(d)}/(p − 1)`,
`j0(d) = min {j ≥ 1 : d p^j ≥ m}`; `τ(n) = n.divisors.card`. We write
`c(d) = 1 − p^{1 − j0(d)}` (`cc p m d`), so that `(p − 1)·w_p(d) = 1 − c(d)`, and `c(d) = 0` as soon
as `d·p ≥ m` (i.e. `d ≥ N1 = ⌈m/p⌉`).

## Results
* `Up_identity`: `(p − 1)·U_p(s) = τ(s) − Σ_{d ∣ s, d·p < m} c(d)`.
* `sbh_identity` (**the S/B/H identity**): for a partition of the primes into `S`, `B`, `H` with
  `y ≤ q ∧ q·p < m` on `B`, `m ≤ q·p` on `H`, `m ≤ y²·p` and `m ≤ y·p²`:
  `(p − 1)·U_p(s) = τ(s_S)·∏_{B ∪ H}(v_q + 1) − F(s_S) − (1 − 1/p)·Σ_{q ∈ B, v_q ≥ 1} a_q(s_S)`,
  `F(n) = Σ_{d ∣ n, d·p < m} c(d)` (`Fsum`), `a_q(n) = #{d ∣ n : d·q·p < m}` (`acount`).
* `Up_identity_tauSplit`: for `m ≤ 2p`, `(p − 1)·U_p(s) = τ(s) − [p < m]·(1 − 1/p)`.
* `max_zero_eq_add`, `expect_hinge_eq` (**the lower-tail identity**):
  `E[(X)⁺] = E[X] + E[(−X)⁺]`.
* `card_divisors_smooth_le_two_pow`, `hinge_tau_split_le` (**τ-split domination**):
  `τ(s_l) ≤ 2^{Σ_l v_q}`, hence `(τ_s τ_l − X)⁺ ≤ (τ_s 2^e − X)⁺`.
* `hingeLoss_eq_sbh`, `hingeLoss_eq_tauSplit`: `Main.hingeLoss` in S/B/H and in τ-split form
  (`E[(… − δ_p (p−1))⁺]/((p−1)(1−δ_p))`).
* `filter_divisors_congr_small`, `Fsum_congr_small`, `acount_congr_small` (**small patterns**): the
  small divisors of `s_S`, hence `F(s_S)` and every `a_q(s_S)`, depend only on `min(v_q, K_q)` when
  `m ≤ q^{K_q + 1}·p`.
-/

namespace MinModulus.Checker2Math

open Finset MinModulus.Smooth

/-! ## `c(d)` -/

/-- `c(d) = 1 − p^{1 − j0(d)}`. -/
noncomputable def cc (p m d : ℕ) : ℝ := 1 - ((p : ℝ)⁻¹) ^ (j0 p m d - 1)

theorem sub_one_mul_wp {p : ℕ} (hp : 1 < p) (m d : ℕ) :
    ((p : ℝ) - 1) * wp p m d = 1 - cc p m d := by
  have h : (p : ℝ) - 1 ≠ 0 := by have := one_lt_cast hp; linarith
  unfold wp cc
  field_simp
  ring

theorem j0_eq_one {p m d : ℕ} (hp : 1 < p) (hd : 0 < d) (h : m ≤ d * p) : j0 p m d = 1 :=
  le_antisymm (j0_le_of hp hd le_rfl (by simpa using h)) (one_le_j0 p m d)

theorem cc_eq_zero {p m d : ℕ} (hp : 1 < p) (hd : 0 < d) (h : m ≤ d * p) : cc p m d = 0 := by
  unfold cc
  rw [j0_eq_one hp hd h]
  simp

theorem j0_eq_two {p m d : ℕ} (hp : 1 < p) (hd : 0 < d) (h1 : d * p < m) (h2 : m ≤ d * p ^ 2) :
    j0 p m d = 2 :=
  j0_eq_of hp hd (by norm_num) h2 (Or.inr (by simpa using h1))

theorem cc_eq_of_two {p m d : ℕ} (hp : 1 < p) (hd : 0 < d) (h1 : d * p < m)
    (h2 : m ≤ d * p ^ 2) : cc p m d = 1 - 1 / (p : ℝ) := by
  unfold cc
  rw [j0_eq_two hp hd h1 h2]
  simp

/-! ## The identity `(p − 1) U_p(s) = τ(s) − Σ_{d ∣ s, d p < m} c(d)` -/

theorem Up_identity {p : ℕ} (hp : 1 < p) (m : ℕ) {s : ℕ} :
    ((p : ℝ) - 1) * Up p m s =
      (s.divisors.card : ℝ) - ∑ d ∈ s.divisors with d * p < m, cc p m d := by
  unfold Up
  rw [mul_sum]
  simp_rw [sub_one_mul_wp hp]
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_filter]
  congr 1
  refine sum_congr rfl fun d hd => ?_
  split_ifs with h
  · rfl
  · exact cc_eq_zero hp (Nat.pos_of_mem_divisors hd) (not_lt.1 h)

/-! ## Divisor sums over coprime products -/

theorem sum_divisors_mul_of_coprime {a b : ℕ} (h : a.Coprime b) (f : ℕ → ℝ) :
    ∑ d ∈ (a * b).divisors, f d = ∑ x ∈ a.divisors, ∑ y ∈ b.divisors, f (x * y) := by
  rw [Nat.divisors_mul, Finset.mul_def,
    sum_image fun x hx y hy hxy => h.mul_injOn_divisors hx hy hxy, sum_product]

/-- A prime factor of a divisor of `s(v)` over a set of primes `R` belongs to `R`. -/
theorem mem_of_prime_dvd_smooth {R : Finset ℕ} (hR : ∀ q ∈ R, q.Prime) {v : ℕ → ℕ} {r : ℕ}
    (hr : r.Prime) (h : r ∣ smooth R v) : r ∈ R := by
  unfold smooth at h
  obtain ⟨q, hq, hrq⟩ := (Prime.dvd_finsetProd_iff hr.prime _).1 h
  have := (Nat.prime_dvd_prime_iff_eq hr (hR q hq)).1 (hr.dvd_of_dvd_pow hrq)
  exact this ▸ hq

/-- A prime `q ∈ R` divides `s(v)` iff `v q ≥ 1`. -/
theorem prime_dvd_smooth_iff {R : Finset ℕ} (hR : ∀ q ∈ R, q.Prime) (v : ℕ → ℕ) {q : ℕ}
    (hq : q ∈ R) : q ∣ smooth R v ↔ 1 ≤ v q := by
  constructor
  · intro h
    have hpos : ∀ r ∈ R, 0 < r := fun r hr => (hR r hr).pos
    have h1 := (hR q hq).factorization_pos_of_dvd (smooth_ne_zero hpos v) h
    simp only [factorization_smooth hR, hq, ↓reduceIte] at h1
    omega
  · intro h
    exact (dvd_pow_self q (by omega)).trans (dvd_prod_of_mem (fun r => r ^ v r) hq)

/-! ## The S/B/H identity -/

/-- `F(n) = Σ_{d ∣ n, d·p < m} c(d)`. -/
noncomputable def Fsum (p m n : ℕ) : ℝ := ∑ d ∈ n.divisors with d * p < m, cc p m d

/-- `a_q(n) = #{d ∣ n : d·q·p < m}`. -/
def acount (p m q n : ℕ) : ℕ := #{d ∈ n.divisors | d * q * p < m}

section SBH

variable {p m y : ℕ} {B H : Finset ℕ}

/-- The divisors `z` of `s_{B ∪ H}(v)` with `x·z·p < m` (`x ≥ 1`) are `1` and the primes `q ∈ B`
with `v q ≥ 1` (two prime factors from `B` give `z ≥ y²`; a prime factor from `H` gives `z·p ≥ m`). -/
theorem filter_divisors_BH (hB : ∀ q ∈ B, q.Prime ∧ y ≤ q ∧ q * p < m)
    (hH : ∀ q ∈ H, q.Prime ∧ m ≤ q * p) (hy2 : m ≤ y * y * p)
    (v : ℕ → ℕ) {x : ℕ} (hx : 0 < x) :
    (smooth (B ∪ H) v).divisors.filter (fun z => x * z * p < m) =
      (insert 1 (B.filter (fun q => 1 ≤ v q))).filter (fun z => x * z * p < m) := by
  have hR : ∀ q ∈ B ∪ H, q.Prime := fun q hq => by
    rcases mem_union.1 hq with h | h
    · exact (hB q h).1
    · exact (hH q h).1
  have hpos : ∀ q ∈ B ∪ H, 0 < q := fun q hq => (hR q hq).pos
  have hs0 : smooth (B ∪ H) v ≠ 0 := smooth_ne_zero hpos v
  -- a prime factor `r` of a divisor `z` with `x z p < m` lies in `B`
  have hfac : ∀ z, z ∣ smooth (B ∪ H) v → x * z * p < m → ∀ r, r.Prime → r ∣ z → r ∈ B := by
    intro z hz hlt r hr hrz
    have hrR := mem_of_prime_dvd_smooth hR hr (hrz.trans hz)
    rcases mem_union.1 hrR with h | h
    · exact h
    · exfalso
      have hz0 : 0 < z := Nat.pos_of_dvd_of_pos hz (Nat.pos_of_ne_zero hs0)
      have hrz' : r ≤ z := Nat.le_of_dvd hz0 hrz
      have := (hH r h).2
      have : r * p ≤ x * z * p := Nat.mul_le_mul_right p (le_trans hrz' (Nat.le_mul_of_pos_left z hx))
      omega
  ext z
  simp only [mem_filter, Nat.mem_divisors, mem_insert]
  constructor
  · rintro ⟨⟨hz, -⟩, hlt⟩
    refine ⟨?_, hlt⟩
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    right
    obtain ⟨r, hr, hrz⟩ := Nat.exists_prime_and_dvd hz1
    have hrB := hfac z hz hlt r hr hrz
    obtain ⟨w, rfl⟩ := hrz
    have hw1 : w = 1 := by
      by_contra hw1
      obtain ⟨r', hr', hr'w⟩ := Nat.exists_prime_and_dvd hw1
      have hr'B := hfac (r * w) hz hlt r' hr' (dvd_mul_of_dvd_right hr'w r)
      have hw0 : 0 < w := Nat.pos_of_mul_pos_left (Nat.pos_of_dvd_of_pos hz (Nat.pos_of_ne_zero hs0))
      have h1 : y ≤ r := (hB r hrB).2.1
      have h2 : y ≤ r' := (hB r' hr'B).2.1
      have h3 : r' ≤ w := Nat.le_of_dvd hw0 hr'w
      have : y * y * p ≤ x * (r * w) * p := by
        apply Nat.mul_le_mul_right
        calc y * y ≤ r * w := Nat.mul_le_mul h1 (h2.trans h3)
          _ ≤ x * (r * w) := Nat.le_mul_of_pos_left _ hx
      omega
    subst hw1
    rw [mul_one] at hz ⊢
    exact ⟨hrB, (prime_dvd_smooth_iff hR v (mem_union_left H hrB)).1 hz⟩
  · rintro ⟨hz, hlt⟩
    refine ⟨⟨?_, hs0⟩, hlt⟩
    rcases hz with rfl | hz
    · exact one_dvd _
    · exact (prime_dvd_smooth_iff hR v (mem_union_left H hz.1)).2 hz.2

/-- The inner sum of the S/B/H identity, for a fixed divisor `x ≥ 1` of `s_S`. -/
theorem inner_sum_BH (hp : 1 < p) (hB : ∀ q ∈ B, q.Prime ∧ y ≤ q ∧ q * p < m)
    (hH : ∀ q ∈ H, q.Prime ∧ m ≤ q * p) (hy2 : m ≤ y * y * p)
    (hy1 : m ≤ y * p ^ 2) (v : ℕ → ℕ) {x : ℕ} (hx : 0 < x) :
    ∑ z ∈ (smooth (B ∪ H) v).divisors with x * z * p < m, cc p m (x * z) =
      (if x * p < m then cc p m x else 0) +
        ∑ q ∈ B with 1 ≤ v q, (if x * q * p < m then 1 - 1 / (p : ℝ) else 0) := by
  have h1 : (1 : ℕ) ∉ B.filter (fun q => 1 ≤ v q) := fun h =>
    (hB 1 (mem_filter.1 h).1).1.one_lt.ne rfl
  rw [filter_divisors_BH hB hH hy2 v hx, sum_filter, sum_insert h1]
  simp only [mul_one]
  congr 1
  refine sum_congr rfl fun q hq => ?_
  split_ifs with hq1
  · have hqB := (mem_filter.1 hq).1
    refine cc_eq_of_two hp (Nat.mul_pos hx (hB q hqB).1.pos) hq1 ?_
    calc m ≤ y * p ^ 2 := hy1
      _ ≤ x * q * p ^ 2 := Nat.mul_le_mul_right _
          (le_trans (hB q hqB).2.1 (Nat.le_mul_of_pos_left q hx))
  · rfl

/-- **The S/B/H identity.** Let `S`, `B`, `H` be sets of primes, `S` disjoint from `B ∪ H`, with
`y ≤ q` and `q·p < m` (i.e. `q < N1 = ⌈m/p⌉`) for `q ∈ B`, `m ≤ q·p` for `q ∈ H`, and
`m ≤ y²·p` (`y² ≥ N1`), `m ≤ y·p²` (`y ≥ N2 = ⌈m/p²⌉`). Then, exactly, for every `v`:
`(p − 1)·U_p(s) = τ(s_S)·∏_{q ∈ B ∪ H}(v_q + 1) − F(s_S) − (1 − 1/p)·Σ_{q ∈ B, v_q ≥ 1} a_q(s_S)`
with `s = s_{S ∪ B ∪ H}(v)`, `s_S = s_S(v)`. -/
theorem sbh_identity (hp : 1 < p) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (hB : ∀ q ∈ B, q.Prime ∧ y ≤ q ∧ q * p < m) (hH : ∀ q ∈ H, q.Prime ∧ m ≤ q * p)
    (hSBH : Disjoint S (B ∪ H)) (hy2 : m ≤ y * y * p) (hy1 : m ≤ y * p ^ 2) (v : ℕ → ℕ) :
    ((p : ℝ) - 1) * Up p m (smooth (S ∪ (B ∪ H)) v) =
      ((smooth S v).divisors.card : ℝ) * ∏ q ∈ B ∪ H, ((v q : ℝ) + 1)
        - Fsum p m (smooth S v)
        - (1 - 1 / (p : ℝ)) * ∑ q ∈ B with 1 ≤ v q, (acount p m q (smooth S v) : ℝ) := by
  have hR : ∀ q ∈ B ∪ H, q.Prime := fun q hq => by
    rcases mem_union.1 hq with h | h
    · exact (hB q h).1
    · exact (hH q h).1
  have hcop : Nat.Coprime (smooth S v) (smooth (B ∪ H) v) :=
    coprime_smooth_of_disjoint hSBH hS hR v v
  have hsplit : smooth (S ∪ (B ∪ H)) v = smooth S v * smooth (B ∪ H) v := by
    unfold smooth
    rw [prod_union hSBH]
  have hinner : ∀ x ∈ (smooth S v).divisors,
      ∑ z ∈ (smooth (B ∪ H) v).divisors, (if x * z * p < m then cc p m (x * z) else 0) =
        (if x * p < m then cc p m x else 0) +
          ∑ q ∈ B with 1 ≤ v q, (if x * q * p < m then 1 - 1 / (p : ℝ) else 0) := by
    intro x hx
    rw [← sum_filter]
    exact inner_sum_BH hp hB hH hy2 hy1 v (Nat.pos_of_mem_divisors hx)
  rw [Up_identity hp, hsplit, Nat.Coprime.card_divisors_mul hcop, Nat.cast_mul,
    card_divisors_smooth_real hR, sum_filter, sum_divisors_mul_of_coprime hcop]
  rw [sum_congr rfl hinner, sum_add_distrib, sum_comm]
  have hF : ∑ x ∈ (smooth S v).divisors, (if x * p < m then cc p m x else 0) =
      Fsum p m (smooth S v) := by
    rw [Fsum, sum_filter]
  have hA : ∀ q ∈ B.filter (fun q => 1 ≤ v q),
      ∑ x ∈ (smooth S v).divisors, (if x * q * p < m then 1 - 1 / (p : ℝ) else 0) =
        (1 - 1 / (p : ℝ)) * (acount p m q (smooth S v) : ℝ) := by
    intro q _
    rw [← sum_filter, sum_const, nsmul_eq_mul, acount, mul_comm]
  rw [hF, sum_congr rfl hA, ← mul_sum]
  ring

end SBH

/-! ## The τ-split case `N1 ≤ 2` -/

/-- For `m ≤ 2p` (i.e. `N1 = ⌈m/p⌉ ≤ 2`) the only divisor `d` with `d·p < m` is `d = 1` (when
`p < m`), and `c(1) = 1 − 1/p` (`j0(1) = 2` since `p < m ≤ 2p ≤ p²`):
`(p − 1)·U_p(s) = τ(s) − [p < m]·(1 − 1/p)`. -/
theorem Up_identity_tauSplit {p m : ℕ} (hp : 1 < p) (hm : m ≤ 2 * p) {s : ℕ} (hs : s ≠ 0) :
    ((p : ℝ) - 1) * Up p m s =
      (s.divisors.card : ℝ) - (if p < m then 1 - 1 / (p : ℝ) else 0) := by
  rw [Up_identity hp]
  congr 1
  have hfilt : s.divisors.filter (fun d => d * p < m) = if p < m then {1} else ∅ := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, hdp⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hs)
      have hd1 : d = 1 := by
        by_contra h
        have : 2 * p ≤ d * p := Nat.mul_le_mul_right p (by omega)
        omega
      subst hd1
      have hpm : p < m := by simpa using hdp
      simp only [hpm, ↓reduceIte, mem_singleton]
    · intro h
      split_ifs at h with hpm
      · rw [mem_singleton] at h
        subst h
        exact ⟨⟨one_dvd s, hs⟩, by simpa using hpm⟩
      · simp at h
  rw [hfilt]
  split_ifs with hpm
  · rw [sum_singleton]
    exact cc_eq_of_two hp one_pos (by simpa using hpm) (by nlinarith)
  · rfl

/-! ## The lower-tail identity -/

/-- `x⁺ = x + (−x)⁺`. -/
theorem max_zero_eq_add (x : ℝ) : max 0 x = x + max 0 (-x) := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

/-- **The lower-tail identity** for the capped tilted law: `E[f⁺] = E[f] + E[(−f)⁺]`. -/
theorem expect_hinge_eq {Ps : Finset ℕ} (ν : ℕ → ℝ) (γ : ℕ → ℕ) (f : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ (fun v => max 0 (f v)) =
      expect Ps ν γ f + expect Ps ν γ (fun v => max 0 (-f v)) := by
  rw [← expect_add]
  exact expect_congr_fun fun v _ => max_zero_eq_add (f v)

/-! ## τ-split domination -/

theorem succ_le_two_pow (a : ℕ) : (a : ℝ) + 1 ≤ 2 ^ a := by
  have := Nat.lt_two_pow_self (n := a)
  exact_mod_cast this

/-- `τ(s_L(v)) ≤ 2^{Σ_{q ∈ L} v_q}` for a set `L` of primes. -/
theorem card_divisors_smooth_le_two_pow {L : Finset ℕ} (hL : ∀ q ∈ L, q.Prime) (v : ℕ → ℕ) :
    ((smooth L v).divisors.card : ℝ) ≤ 2 ^ (∑ q ∈ L, v q) := by
  rw [card_divisors_smooth_real hL, ← prod_pow_eq_pow_sum]
  exact prod_le_prod₀ (fun q _ => by positivity) fun q _ => succ_le_two_pow (v q)

/-- **τ-split domination**: `(τ_s·τ_l − X)⁺ ≤ (τ_s·2^e − X)⁺` for `0 ≤ τ_s` and `τ_l ≤ 2^e`. -/
theorem hinge_tau_split_le {τs τl e X : ℝ} (hs : 0 ≤ τs) (hl : τl ≤ e) :
    max 0 (τs * τl - X) ≤ max 0 (τs * e - X) :=
  max_le_max le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_left hl hs) X)


/-! ## Bridges to `Main.hingeLoss` -/

/-- Pointwise rescaling: `(U − t)⁺/(1 − t) = ((p−1)U − t(p−1))⁺/((p−1)(1−t))` for `p > 1`. -/
theorem hinge_div_rescale {p : ℕ} (hp : 1 < p) (u t : ℝ) :
    max 0 (u - t) / (1 - t) = max 0 (((p : ℝ) - 1) * u - t * ((p : ℝ) - 1)) /
      (((p : ℝ) - 1) * (1 - t)) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by have := one_lt_cast hp; linarith
  have : ((p : ℝ) - 1) * u - t * ((p : ℝ) - 1) = ((p : ℝ) - 1) * (u - t) := by ring
  have hm : max 0 (((p : ℝ) - 1) * (u - t)) = ((p : ℝ) - 1) * max 0 (u - t) := by
    rw [mul_max_of_nonneg _ _ hp1.le, mul_zero]
  rw [this, hm, mul_div_mul_left _ _ hp1.ne']

/-- **`hingeLoss` in S/B/H form.** For a prime `p`, a partition `primesBelow p = S ∪ (B ∪ H)`
satisfying the hypotheses of `sbh_identity`, and `δ p < 1`:
`hingeLoss m δ p γ = E[(τ(s_S)·T − F(s_S) − (1 − 1/p)·b − δ_p (p−1))⁺] / ((p−1)(1−δ_p))`
(expectation over `primesBelow p`, tilts `tilt δ`, caps `γ`). -/
theorem hingeLoss_eq_sbh {m p y : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) {S B H : Finset ℕ}
    (hpart : Nat.primesBelow p = S ∪ (B ∪ H)) (hSBH : Disjoint S (B ∪ H))
    (hB : ∀ q ∈ B, y ≤ q ∧ q * p < m) (hH : ∀ q ∈ H, m ≤ q * p) (hy2 : m ≤ y * y * p)
    (hy1 : m ≤ y * p ^ 2) (γ : ℕ → ℕ) :
    Main.hingeLoss m δ p γ =
      expect (Nat.primesBelow p) (Main.tilt δ) γ (fun v => max 0
        (((smooth S v).divisors.card : ℝ) * ∏ q ∈ B ∪ H, ((v q : ℝ) + 1)
          - Fsum p m (smooth S v)
          - (1 - 1 / (p : ℝ)) * ∑ q ∈ B with 1 ≤ v q, (acount p m q (smooth S v) : ℝ)
          - δ p * ((p : ℝ) - 1))) / (((p : ℝ) - 1) * (1 - δ p)) := by
  have hpr : ∀ q ∈ S ∪ (B ∪ H), q.Prime := fun q hq =>
    Nat.prime_of_mem_primesBelow (hpart ▸ hq)
  have hS : ∀ q ∈ S, q.Prime := fun q hq => hpr q (mem_union_left _ hq)
  have hB' : ∀ q ∈ B, q.Prime ∧ y ≤ q ∧ q * p < m := fun q hq =>
    ⟨hpr q (mem_union_right _ (mem_union_left _ hq)), hB q hq⟩
  have hH' : ∀ q ∈ H, q.Prime ∧ m ≤ q * p := fun q hq =>
    ⟨hpr q (mem_union_right _ (mem_union_right _ hq)), hH q hq⟩
  unfold Main.hingeLoss
  rw [div_eq_mul_inv, ← expect_mul_const]
  refine expect_congr_fun fun v _ => ?_
  rw [← div_eq_mul_inv, hinge_div_rescale hp.one_lt, hpart,
    sbh_identity hp.one_lt hS hB' hH' hSBH hy2 hy1 v]

/-- **`hingeLoss` in τ-split form** (`m ≤ 2p`, i.e. `N1 ≤ 2`):
`hingeLoss m δ p γ = E[(τ(s) − [p < m](1 − 1/p) − δ_p (p−1))⁺] / ((p−1)(1−δ_p))`. -/
theorem hingeLoss_eq_tauSplit {m p : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) (hm : m ≤ 2 * p)
    (γ : ℕ → ℕ) :
    Main.hingeLoss m δ p γ =
      expect (Nat.primesBelow p) (Main.tilt δ) γ (fun v => max 0
        (((smooth (Nat.primesBelow p) v).divisors.card : ℝ)
          - (if p < m then 1 - 1 / (p : ℝ) else 0) - δ p * ((p : ℝ) - 1))) /
        (((p : ℝ) - 1) * (1 - δ p)) := by
  unfold Main.hingeLoss
  rw [div_eq_mul_inv, ← expect_mul_const]
  refine expect_congr_fun fun v _ => ?_
  have hpos : ∀ q ∈ Nat.primesBelow p, 0 < q := fun q hq => (Nat.prime_of_mem_primesBelow hq).pos
  rw [← div_eq_mul_inv, hinge_div_rescale hp.one_lt,
    Up_identity_tauSplit hp.one_lt hm (smooth_ne_zero hpos v)]

/-! ## Small patterns: `F` and the profile depend only on truncated exponents -/

/-- A divisor `d` of `s_S(v)` with `d·p < m` divides `s_S(w)` whenever `v` and `w` agree after
truncation at `K q`, where `m ≤ q^{K q + 1}·p` (so `q^e·p < m` forces `e ≤ K q`). -/
theorem dvd_smooth_of_small {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p m : ℕ} {K : ℕ → ℕ}
    (hK : ∀ q ∈ S, m ≤ q ^ (K q + 1) * p) {v w : ℕ → ℕ}
    (hvw : ∀ q ∈ S, min (v q) (K q) = min (w q) (K q)) {d : ℕ} (hd : d ∣ smooth S v)
    (hdp : d * p < m) : d ∣ smooth S w := by
  have hpos : ∀ q ∈ S, 0 < q := fun q hq => (hS q hq).pos
  have hv0 := smooth_ne_zero hpos v
  have hw0 := smooth_ne_zero hpos w
  have hd0 : d ≠ 0 := fun h => hv0 (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  rw [← Nat.factorization_le_iff_dvd hd0 hw0]
  intro r
  have hle := (Nat.factorization_le_iff_dvd hd0 hv0).2 hd r
  rw [factorization_smooth hS] at hle ⊢
  by_cases hr : r ∈ S
  · simp only [hr, ↓reduceIte] at hle ⊢
    have he : d.factorization r ≤ K r := by
      by_contra hcon
      have h1 : r ^ (K r + 1) ∣ d :=
        (Nat.pow_dvd_pow r (by omega)).trans (Nat.ordProj_dvd d r)
      have h2 : r ^ (K r + 1) ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) h1
      have h3 := hK r hr
      have : r ^ (K r + 1) * p ≤ d * p := Nat.mul_le_mul_right p h2
      omega
    have := hvw r hr
    have h4 : d.factorization r ≤ min (v r) (K r) := le_min hle he
    rw [this] at h4
    exact h4.trans (min_le_left _ _)
  · simp only [hr, ↓reduceIte] at hle ⊢
    exact hle

/-- The small divisors (`d·p < m`) of `s_S(v)` depend only on the truncated exponents
`min (v q) (K q)` (the **small pattern**), when `m ≤ q^{K q + 1}·p` for `q ∈ S`. Hence so do
`F(s_S)` (`Fsum_congr_small`) and every `a_q(s_S)` (`acount_congr_small`). -/
theorem filter_divisors_congr_small {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p m : ℕ} {K : ℕ → ℕ}
    (hK : ∀ q ∈ S, m ≤ q ^ (K q + 1) * p) {v w : ℕ → ℕ}
    (hvw : ∀ q ∈ S, min (v q) (K q) = min (w q) (K q)) :
    (smooth S v).divisors.filter (fun d => d * p < m) =
      (smooth S w).divisors.filter (fun d => d * p < m) := by
  have hpos : ∀ q ∈ S, 0 < q := fun q hq => (hS q hq).pos
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, hdp⟩
    exact ⟨⟨dvd_smooth_of_small hS hK hvw hd hdp, smooth_ne_zero hpos w⟩, hdp⟩
  · rintro ⟨⟨hd, -⟩, hdp⟩
    exact ⟨⟨dvd_smooth_of_small hS hK (fun q hq => (hvw q hq).symm) hd hdp,
      smooth_ne_zero hpos v⟩, hdp⟩

theorem Fsum_congr_small {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p m : ℕ} {K : ℕ → ℕ}
    (hK : ∀ q ∈ S, m ≤ q ^ (K q + 1) * p) {v w : ℕ → ℕ}
    (hvw : ∀ q ∈ S, min (v q) (K q) = min (w q) (K q)) :
    Fsum p m (smooth S v) = Fsum p m (smooth S w) := by
  unfold Fsum
  rw [filter_divisors_congr_small hS hK hvw]

theorem acount_congr_small {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p m : ℕ} {K : ℕ → ℕ}
    (hK : ∀ q ∈ S, m ≤ q ^ (K q + 1) * p) {v w : ℕ → ℕ}
    (hvw : ∀ q ∈ S, min (v q) (K q) = min (w q) (K q)) (q : ℕ) (hq : 0 < q) :
    acount p m q (smooth S v) = acount p m q (smooth S w) := by
  unfold acount
  have e : ∀ n : ℕ, n.divisors.filter (fun d => d * q * p < m) =
      (n.divisors.filter (fun d => d * p < m)).filter (fun d => d * q * p < m) := by
    intro n
    rw [filter_filter]
    refine filter_congr fun d _ => ?_
    constructor
    · intro h
      refine ⟨?_, h⟩
      calc d * p ≤ d * q * p := Nat.mul_le_mul_right p (Nat.le_mul_of_pos_right d hq)
        _ < m := h
    · exact fun h => h.2
  rw [e, e, filter_divisors_congr_small hS hK hvw]

end MinModulus.Checker2Math
