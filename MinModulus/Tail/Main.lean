import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Tail: elementary Chebyshev tail bound (replaces BBMST Theorem 6.1 / Dusart)

## Status
**Done, sorry-free.** `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for
every public theorem. Imports only Mathlib, and no other `MinModulus` module.

## Main results (`g q = 2(3q−1)/(q−1)^2`)
* `tail_bound`: for `X ≥ 2^27` and a finite set `S` of primes, all `> X`,
  `Σ_{p∈S} (Π_{q∈S, q<p} (1 + g q)) / (p−1)^2 ≤ 100/(189 X)`. Here `C = 100/189 ≈ 0.529101`.
* `tail_bound_53`: the same with the target constant `53/(100 X)`.
* `tail_bound_of_le`: factors `1 + h q` with `0 ≤ h q ≤ g q`, for `q ∈ S`.
* `tail_bound_family`: indexed by a finset `s` of a linear order (e.g. levels `Fin n`), with
  `P : ι → ℕ` `StrictMonoOn` on `s`, primes `P i > X`, and index-dependent `0 ≤ h i ≤ g (P i)`.
  The product runs over `j ∈ s, j < i`.
* `tail_bound_family_nu`: `h j = ν j * (3 P_j − 1)/(P_j − 1)^2`, with `0 ≤ ν j ≤ 2`.
* `tail_bound_2e8`, `tail_bound_family_nu_2e8`: at `X = 2·10^8`, the sum is `< 265/10^11`
  (`= 2.65·10^{-9}`); the proved bound is `100/(189·2·10^8) ≈ 2.6455·10^{-9}`.

## Interface notes (relative to LEAN_DESIGN.md §3)
* The constant is `100/189`, which is below `53/100`; `tail_bound_53` gives the design's form.
* The statements are written out with no local definitions, so users need not unfold `g`.
  `tail_bound_g` is the same statement phrased with `g`.

## Proof
1. Chebyshev. The primes of a set `T ⊆ (n, 2n]` have a product dividing `C(2n, n) ≤ 4^n`, so
   `n^{#T} ≤ 4^n`. With `n ≥ 2^27` this gives `27 #T ≤ 2n` (`card_block_le`).
2. Dyadic blocks `blk X q = log₂ ⌊(q−1)/X⌋`, so `X 2^J < q ≤ X 2^{J+1}`. For `q > n ≥ 4000`,
   `g q ≤ 6.001/n` (`g_le`). Hence the product over one block is at most
   `exp(#T · 6.001/n) ≤ exp(6001/13500) ≤ 25/16` (`prod_block_le`, `exp_L_le` via `Real.exp_bound'`).
3. For `p` in block `J`, `Π_{q<p} ≤ (25/16)^{J+1}` (`prod_lt_le`) and `(p−1)^2 ≥ (X 2^J)^2`.
   Block `J` then contributes at most `(2 X 2^J/27)(25/16)^{J+1}/(X 2^J)^2 = (25/(216 X))(25/32)^J`.
4. Geometric series: `Σ_J (25/32)^J ≤ 32/7`, giving `(25/216)(32/7)/X = 100/(189 X)`.
-/

namespace MinModulus.Tail

open Finset

/-- `g q = 2(3q-1)/(q-1)^2`. -/
noncomputable def g (q : ℕ) : ℝ := 2 * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2

/-! ### Chebyshev count of primes in a dyadic block -/

/-- A set `T` of primes in `(n, 2n]` satisfies `n ^ #T ≤ 4 ^ n`:
the product of the primes of `T` divides `C(2n, n) ≤ 4 ^ n`. -/
theorem pow_card_le_four_pow {n : ℕ} (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ n < p ∧ p ≤ 2 * n) : n ^ T.card ≤ 4 ^ n := by
  have hdvd : ∏ p ∈ T, p ∣ Nat.choose (n + n) n :=
    Finset.prod_primes_dvd _ (fun p hp => (hT p hp).1.prime) (fun p hp => by
      obtain ⟨hp, h1, h2⟩ := hT p hp
      exact hp.dvd_choose_add h1 h1 (by omega))
  have hpos : 0 < Nat.choose (n + n) n := Nat.choose_pos (by omega)
  calc n ^ T.card ≤ ∏ p ∈ T, p := Finset.pow_card_le_prod _ _ _ fun p hp => (hT p hp).2.1.le
    _ ≤ Nat.choose (n + n) n := Nat.le_of_dvd hpos hdvd
    _ = Nat.centralBinom n := by rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
    _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n

/-- If `n ≥ 2^27`, a set of primes in `(n, 2n]` has at most `2n/27` elements. -/
theorem card_block_le {n : ℕ} (hn : 2 ^ 27 ≤ n) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ n < p ∧ p ≤ 2 * n) : 27 * T.card ≤ 2 * n := by
  have h3 : 2 ^ (27 * T.card) ≤ 2 ^ (2 * n) :=
    calc 2 ^ (27 * T.card) = (2 ^ 27) ^ T.card := pow_mul 2 27 T.card
      _ ≤ n ^ T.card := Nat.pow_le_pow_left hn _
      _ ≤ 4 ^ n := pow_card_le_four_pow T hT
      _ = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

/-! ### Numerical facts about `g` and `exp` -/

theorem exp_L_le : Real.exp (6001 / 13500) ≤ 25 / 16 := by
  have h := Real.exp_bound' (x := 6001 / 13500) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

theorem g_nonneg {q : ℕ} (hq : 1 ≤ q) : 0 ≤ g q := by
  unfold g
  have : (1 : ℝ) ≤ q := by exact_mod_cast hq
  apply div_nonneg _ (sq_nonneg _)
  linarith

theorem g_le {n q : ℕ} (hn : 4000 ≤ n) (hq : n < q) : g q ≤ 6001 / 1000 / n := by
  unfold g
  have hn' : (4000 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (n : ℝ) + 1 ≤ q := by exact_mod_cast hq
  have hu : (n : ℝ) ≤ (q : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hupos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) hnpos]
  nlinarith [mul_le_mul_of_nonneg_left hu hupos.le,
    mul_nonneg (sub_nonneg.2 (hn'.trans hu)) hupos.le]

/-- The product over one dyadic block is at most `exp (2 · 6.001 / 27) ≤ 25/16`. -/
theorem prod_block_le {n : ℕ} (hn : 2 ^ 27 ≤ n) (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ n < p ∧ p ≤ 2 * n) :
    ∏ q ∈ T, (1 + g q) ≤ 25 / 16 := by
  have hcard : (27 : ℝ) * T.card ≤ 2 * n := by exact_mod_cast card_block_le hn T hT
  have hn4000 : 4000 ≤ n := le_trans (by norm_num) hn
  have hnpos : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  calc ∏ q ∈ T, (1 + g q) ≤ ∏ q ∈ T, Real.exp (g q) := by
        apply Finset.prod_le_prod₀
        · intro q hq
          have := g_nonneg (q := q) (by have := (hT q hq).2.1; omega)
          linarith
        · intro q _
          rw [add_comm]; exact Real.add_one_le_exp _
    _ = Real.exp (∑ q ∈ T, g q) := (Real.exp_sum T g).symm
    _ ≤ Real.exp (6001 / 13500) := by
        apply Real.exp_le_exp.2
        calc ∑ q ∈ T, g q ≤ ∑ _q ∈ T, (6001 / 1000 / (n : ℝ)) :=
              Finset.sum_le_sum fun q hq => g_le hn4000 (hT q hq).2.1
          _ = T.card * (6001 / 1000 / (n : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 6001 / 13500 := by
              rw [mul_div_assoc', div_le_iff₀ hnpos]
              linarith
    _ ≤ 25 / 16 := exp_L_le

/-! ### Dyadic block index -/

/-- The dyadic block index: for `0 < X < q`, `X * 2^(blk X q) < q ≤ X * 2^(blk X q + 1)`. -/
def blk (X q : ℕ) : ℕ := Nat.log 2 ((q - 1) / X)

theorem blk_spec {X q : ℕ} (hX : 0 < X) (hq : X < q) :
    X * 2 ^ blk X q < q ∧ q ≤ 2 * (X * 2 ^ blk X q) := by
  have h1 : (q - 1) / X ≠ 0 := (Nat.div_pos (by omega) hX).ne'
  have hlo := (Nat.le_div_iff_mul_le hX).1 (Nat.pow_log_le_self 2 h1)
  have hhi := (Nat.div_lt_iff_lt_mul hX).1 (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((q - 1) / X))
  unfold blk
  rw [pow_succ] at hhi
  generalize 2 ^ Nat.log 2 ((q - 1) / X) = N at *
  have e1 : N * X = X * N := mul_comm _ _
  have e2 : N * 2 * X = 2 * (X * N) := by ring
  rw [e1] at hlo
  rw [e2] at hhi
  generalize X * N = M at *
  omega

theorem blk_mono (X : ℕ) {q p : ℕ} (h : q ≤ p) : blk X q ≤ blk X p :=
  Nat.log_mono_right (Nat.div_le_div_right (by omega))

/-- Primes of `S` in block `j` lie in `(X 2^j, 2 X 2^j]`. -/
theorem mem_block {X : ℕ} (hX0 : 0 < X) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ X < p)
    {T : Finset ℕ} (hTS : T ⊆ S) {j : ℕ} (hTj : ∀ q ∈ T, blk X q = j) :
    ∀ q ∈ T, q.Prime ∧ X * 2 ^ j < q ∧ q ≤ 2 * (X * 2 ^ j) := by
  intro q hq
  obtain ⟨hprime, hXq⟩ := hS q (hTS hq)
  have := blk_spec hX0 hXq
  rw [hTj q hq] at this
  exact ⟨hprime, this.1, this.2⟩

theorem two_pow_27_le {X : ℕ} (hX : 2 ^ 27 ≤ X) (j : ℕ) : 2 ^ 27 ≤ X * 2 ^ j :=
  hX.trans (Nat.le_mul_of_pos_right _ (by positivity))

/-! ### The product over the smaller primes -/

theorem prod_lt_le (X : ℕ) (hX : 2 ^ 27 ≤ X) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ X < p) {p : ℕ} :
    ∏ q ∈ S with q < p, (1 + g q) ≤ (25 / 16 : ℝ) ^ (blk X p + 1) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hmaps : ∀ q ∈ S.filter (· < p), blk X q ∈ range (blk X p + 1) := by
    intro q hq
    rw [mem_filter] at hq
    exact mem_range.2 (Nat.lt_succ_of_le (blk_mono X hq.2.le))
  rw [← Finset.prod_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∏ _j ∈ range (blk X p + 1), (25 / 16 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro j _
          apply Finset.prod_nonneg
          intro q hq
          have hqS : q ∈ S := (mem_filter.1 (mem_filter.1 hq).1).1
          have := g_nonneg (q := q) (by have := (hS q hqS).2; omega)
          linarith
        · intro j _
          apply prod_block_le (two_pow_27_le hX j)
          apply mem_block hX0 hS
          · intro q hq; exact (mem_filter.1 (mem_filter.1 hq).1).1
          · intro q hq; exact (mem_filter.1 hq).2
    _ = (25 / 16 : ℝ) ^ (blk X p + 1) := by rw [Finset.prod_const, Finset.card_range]

/-! ### Main theorem -/

theorem tail_bound_g (X : ℕ) (hX : 2 ^ 27 ≤ X) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ X < p) :
    ∑ p ∈ S, (∏ q ∈ S with q < p, (1 + g q)) / ((p : ℝ) - 1) ^ 2 ≤ 100 / (189 * (X : ℝ)) := by
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX0
  have hXne : (X : ℝ) ≠ 0 := hXr.ne'
  have hmaps : ∀ p ∈ S, blk X p ∈ range (S.sup (blk X) + 1) := fun p hp =>
    mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := blk X) hp))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ J ∈ range (S.sup (blk X) + 1), ∑ p ∈ S with blk X p = J,
          (25 / 16 : ℝ) ^ (J + 1) / ((X : ℝ) * 2 ^ J) ^ 2 := by
        apply Finset.sum_le_sum; intro J _
        apply Finset.sum_le_sum; intro p hp
        rw [mem_filter] at hp
        obtain ⟨hpS, hpJ⟩ := hp
        have hspec := blk_spec hX0 (hS p hpS).2
        rw [hpJ] at hspec
        have h1 : ((X * 2 ^ J + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hspec.1
        push_cast at h1
        have hpos : (0 : ℝ) < (X : ℝ) * 2 ^ J := by positivity
        apply div_le_div₀ (by positivity) _ (by positivity) _
        · rw [← hpJ]; exact prod_lt_le X hX S hS
        · exact pow_le_pow_left₀ hpos.le (by linarith) 2
    _ = ∑ J ∈ range (S.sup (blk X) + 1), ((S.filter (fun p => blk X p = J)).card : ℝ) *
          ((25 / 16 : ℝ) ^ (J + 1) / ((X : ℝ) * 2 ^ J) ^ 2) := by
        apply Finset.sum_congr rfl; intro J _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ J ∈ range (S.sup (blk X) + 1), (2 * ((X : ℝ) * 2 ^ J) / 27) *
          ((25 / 16 : ℝ) ^ (J + 1) / ((X : ℝ) * 2 ^ J) ^ 2) := by
        apply Finset.sum_le_sum; intro J _
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc := card_block_le (two_pow_27_le hX J) (S.filter (fun p => blk X p = J))
          (mem_block hX0 hS (filter_subset _ _) (fun q hq => (mem_filter.1 hq).2))
        have : (27 : ℝ) * ((S.filter (fun p => blk X p = J)).card : ℝ) ≤
            2 * ((X * 2 ^ J : ℕ) : ℝ) := by exact_mod_cast hc
        push_cast at this
        linarith
    _ = ∑ J ∈ range (S.sup (blk X) + 1), 25 / (216 * (X : ℝ)) * (25 / 32 : ℝ) ^ J := by
        apply Finset.sum_congr rfl; intro J _
        rw [show (25 / 32 : ℝ) ^ J = (25 / 16 : ℝ) ^ J / 2 ^ J by rw [← div_pow]; norm_num,
          pow_succ]
        field_simp
        ring
    _ = 25 / (216 * (X : ℝ)) * ∑ J ∈ range (S.sup (blk X) + 1), (25 / 32 : ℝ) ^ J := by
        rw [Finset.mul_sum]
    _ ≤ 25 / (216 * (X : ℝ)) * (32 / 7) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := geom_sum_Ico_le_of_lt_one (x := (25 / 32 : ℝ)) (m := 0)
          (n := S.sup (blk X) + 1) (by norm_num) (by norm_num)
        rw [← Finset.range_eq_Ico] at this
        norm_num at this ⊢
        linarith
    _ = 100 / (189 * (X : ℝ)) := by field_simp; ring

/-! ### Public statements -/

/-- **Tail bound** (explicit form, `C = 100/189 ≈ 0.52910`). For every natural `X ≥ 2^27` and
every finite set `S` of primes, all `> X`,
`Σ_{p∈S} (Π_{q∈S, q<p} (1 + 2(3q−1)/(q−1)^2)) / (p−1)^2 ≤ 100/(189 X)`. -/
theorem tail_bound (X : ℕ) (hX : 2 ^ 27 ≤ X) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ X < p) :
    ∑ p ∈ S, (∏ q ∈ S with q < p, (1 + 2 * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2)) /
      ((p : ℝ) - 1) ^ 2 ≤ 100 / (189 * (X : ℝ)) :=
  tail_bound_g X hX S hS

/-- The tail bound with the target constant `C = 53/100`. -/
theorem tail_bound_53 (X : ℕ) (hX : 2 ^ 27 ≤ X) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ X < p) :
    ∑ p ∈ S, (∏ q ∈ S with q < p, (1 + 2 * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2)) /
      ((p : ℝ) - 1) ^ 2 ≤ 53 / (100 * (X : ℝ)) := by
  refine (tail_bound X hX S hS).trans ?_
  have hXr : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hX : 0 < X)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- The tail bound for any factors `0 ≤ h q ≤ g q` (e.g. `h q = ν_q (3q−1)/(q−1)^2`, `ν_q ≤ 2`). -/
theorem tail_bound_of_le (X : ℕ) (hX : 2 ^ 27 ≤ X) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ X < p) (h : ℕ → ℝ) (h0 : ∀ q ∈ S, 0 ≤ h q)
    (hle : ∀ q ∈ S, h q ≤ 2 * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2) :
    ∑ p ∈ S, (∏ q ∈ S with q < p, (1 + h q)) / ((p : ℝ) - 1) ^ 2 ≤ 100 / (189 * (X : ℝ)) := by
  refine le_trans (Finset.sum_le_sum fun p _ => ?_) (tail_bound_g X hX S hS)
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.prod_le_prod₀
  · intro q hq; have := h0 q (mem_filter.1 hq).1; linarith
  · intro q hq; have := hle q (mem_filter.1 hq).1; unfold g; linarith

/-- The tail bound for a strictly increasing family of primes `P i > X` indexed by a finset `s` of
a linear order (e.g. the levels `Fin n` of the product space), with index-dependent factors
`0 ≤ h i ≤ g (P i)`. The product runs over the indices `j ∈ s` with `j < i`. -/
theorem tail_bound_family {ι : Type*} [LinearOrder ι] (X : ℕ) (hX : 2 ^ 27 ≤ X)
    (s : Finset ι) (P : ι → ℕ) (hP : StrictMonoOn P s)
    (hS : ∀ i ∈ s, (P i).Prime ∧ X < P i) (h : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ h i)
    (hle : ∀ i ∈ s, h i ≤ 2 * (3 * (P i : ℝ) - 1) / ((P i : ℝ) - 1) ^ 2) :
    ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + h j)) / ((P i : ℝ) - 1) ^ 2 ≤ 100 / (189 * (X : ℝ)) := by
  have hinj : Set.InjOn P s := hP.injOn
  have hSimg : ∀ p ∈ s.image P, p.Prime ∧ X < p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hp
    exact hS i hi
  have key : ∀ i ∈ s, ∏ j ∈ s with j < i, (1 + g (P j)) =
      ∏ q ∈ s.image P with q < P i, (1 + g q) := by
    intro i hi
    have hfil : (s.image P).filter (· < P i) = (s.filter (· < i)).image P := by
      ext q
      simp only [mem_filter, mem_image]
      constructor
      · rintro ⟨⟨j, hj, rfl⟩, hlt⟩
        exact ⟨j, ⟨hj, (hP.lt_iff_lt hj hi).1 hlt⟩, rfl⟩
      · rintro ⟨j, ⟨hj, hlt⟩, rfl⟩
        exact ⟨⟨j, hj, rfl⟩, hP hj hi hlt⟩
    rw [hfil, Finset.prod_image (fun a ha b hb hab =>
      hinj (mem_filter.1 ha).1 (mem_filter.1 hb).1 hab)]
  calc ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + h j)) / ((P i : ℝ) - 1) ^ 2
      ≤ ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + g (P j))) / ((P i : ℝ) - 1) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply Finset.prod_le_prod₀
        · intro j hj; have := h0 j (mem_filter.1 hj).1; linarith
        · intro j hj; have := hle j (mem_filter.1 hj).1; unfold g; linarith
    _ = ∑ i ∈ s, (∏ q ∈ s.image P with q < P i, (1 + g q)) / ((P i : ℝ) - 1) ^ 2 := by
        apply Finset.sum_congr rfl; intro i hi; rw [key i hi]
    _ = ∑ p ∈ s.image P, (∏ q ∈ s.image P with q < p, (1 + g q)) / ((p : ℝ) - 1) ^ 2 := by
        rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
    _ ≤ 100 / (189 * (X : ℝ)) := tail_bound_g X hX _ hSimg

/-- The family version with tilts: factors `1 + ν_j (3 P_j − 1)/(P_j − 1)^2` with `0 ≤ ν_j ≤ 2`. -/
theorem tail_bound_family_nu {ι : Type*} [LinearOrder ι] (X : ℕ) (hX : 2 ^ 27 ≤ X)
    (s : Finset ι) (P : ι → ℕ) (hP : StrictMonoOn P s)
    (hS : ∀ i ∈ s, (P i).Prime ∧ X < P i) (ν : ι → ℝ) (hν0 : ∀ i ∈ s, 0 ≤ ν i)
    (hν2 : ∀ i ∈ s, ν i ≤ 2) :
    ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)) /
      ((P i : ℝ) - 1) ^ 2 ≤ 100 / (189 * (X : ℝ)) := by
  have hbase : ∀ i ∈ s, 0 ≤ (3 * (P i : ℝ) - 1) / ((P i : ℝ) - 1) ^ 2 := by
    intro i hi
    have : (1 : ℝ) ≤ P i := by exact_mod_cast (hS i hi).1.one_lt.le
    exact div_nonneg (by linarith) (sq_nonneg _)
  refine tail_bound_family X hX s P hP hS (fun j => ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)
    (fun i hi => ?_) (fun i hi => ?_)
  · simp only [mul_div_assoc]
    exact mul_nonneg (hν0 i hi) (hbase i hi)
  · simp only [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (hν2 i hi) (hbase i hi)

/-! ### Corollaries at `X = 2·10^8` -/

/-- At `X = 2·10^8` the tail sum is `< 2.65·10^{-9}` (the bound is `100/(189·2·10^8) ≈ 2.6455e-9`). -/
theorem tail_bound_2e8 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 * 10 ^ 8 < p) :
    ∑ p ∈ S, (∏ q ∈ S with q < p, (1 + 2 * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2)) /
      ((p : ℝ) - 1) ^ 2 < 265 / 10 ^ 11 := by
  refine (tail_bound (2 * 10 ^ 8) (by norm_num) S hS).trans_lt ?_
  norm_num

/-- Family version at `X = 2·10^8`, with tilts `0 ≤ ν_j ≤ 2`. -/
theorem tail_bound_family_nu_2e8 {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (P : ι → ℕ) (hP : StrictMonoOn P s)
    (hS : ∀ i ∈ s, (P i).Prime ∧ 2 * 10 ^ 8 < P i) (ν : ι → ℝ) (hν0 : ∀ i ∈ s, 0 ≤ ν i)
    (hν2 : ∀ i ∈ s, ν i ≤ 2) :
    ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)) /
      ((P i : ℝ) - 1) ^ 2 < 265 / 10 ^ 11 := by
  refine (tail_bound_family_nu (2 * 10 ^ 8) (by norm_num) s P hP hS ν hν0 hν2).trans_lt ?_
  norm_num

end MinModulus.Tail
