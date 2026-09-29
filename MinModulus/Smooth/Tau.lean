import MinModulus.Smooth.Config
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Module 4 (`Smooth`), part 3: the divisor function of `s(v)`

* `card_divisors_smooth` : `τ(s(v)) = Π_{q ∈ Ps} (v q + 1)` when `Ps` consists of primes
  (for every `v`, in or out of the box);
* (vii) `expect_tau_rpow` : `E[τ(s)^θ] = Π_{q ∈ Ps} E_q[(v q + 1)^θ]` (real `θ`, `Real.rpow`),
  and `expect_tau_pow` for natural exponents.

Here `τ(n)` is written `(n.divisors.card : ℝ)`.
-/

namespace MinModulus.Smooth

open Finset

variable {Ps : Finset ℕ}

theorem card_divisors_prime_pow {q : ℕ} (hq : q.Prime) (k : ℕ) : (q ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hq, card_map, card_range]

theorem coprime_pow_smooth {q : ℕ} (hq : q.Prime) (hqPs : q ∉ Ps) (hPs : ∀ r ∈ Ps, r.Prime)
    (k : ℕ) (v : ℕ → ℕ) : Nat.Coprime (q ^ k) (smooth Ps v) := by
  apply Nat.Coprime.pow_left
  unfold smooth
  rw [Nat.coprime_prod_right_iff]
  intro r hr
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_primes hq (hPs r hr)]
  rintro rfl
  exact hqPs hr

/-- `τ(s(v)) = Π_{q ∈ Ps} (v q + 1)` when `Ps` consists of primes. -/
theorem card_divisors_smooth (hPs : ∀ q ∈ Ps, q.Prime) (v : ℕ → ℕ) :
    (smooth Ps v).divisors.card = ∏ q ∈ Ps, (v q + 1) := by
  induction Ps using Finset.induction_on with
  | empty => simp
  | insert q Ps hq ih =>
    have hq' : q.Prime := hPs q (mem_insert_self q Ps)
    have hPs' : ∀ r ∈ Ps, r.Prime := fun r hr => hPs r (mem_insert_of_mem hr)
    rw [smooth_insert hq, Nat.Coprime.card_divisors_mul (coprime_pow_smooth hq' hq hPs' _ v),
      card_divisors_prime_pow hq', ih hPs', prod_insert hq]

theorem card_divisors_smooth_real (hPs : ∀ q ∈ Ps, q.Prime) (v : ℕ → ℕ) :
    ((smooth Ps v).divisors.card : ℝ) = ∏ q ∈ Ps, ((v q : ℝ) + 1) := by
  rw [card_divisors_smooth hPs]
  push_cast
  rfl

/-! ### Factorization of `s(v)`; divisors of `s(v)` are the `s(b)` with `b ≤ v` -/

/-- The `r`-adic valuation of `s(v)` is `v r` for `r ∈ Ps` and `0` otherwise. -/
theorem factorization_smooth (hPs : ∀ q ∈ Ps, q.Prime) (v : ℕ → ℕ) (r : ℕ) :
    (smooth Ps v).factorization r = if r ∈ Ps then v r else 0 := by
  induction Ps using Finset.induction_on with
  | empty => simp
  | insert q Ps hq ih =>
    have hq' : q.Prime := hPs q (mem_insert_self q Ps)
    have hPs' : ∀ r ∈ Ps, r.Prime := fun r hr => hPs r (mem_insert_of_mem hr)
    have hpos : ∀ r ∈ Ps, 0 < r := fun r hr => (hPs' r hr).pos
    rw [smooth_insert hq, Nat.factorization_mul (pow_ne_zero _ hq'.ne_zero)
      (smooth_ne_zero hpos v), Finsupp.add_apply, hq'.factorization_pow, ih hPs',
      Finsupp.single_apply]
    by_cases hrq : q = r
    · subst hrq
      simp [hq]
    · have : r ≠ q := fun h => hrq h.symm
      simp [hrq, this]

/-- `s` is injective on configurations supported in `Ps` (unique factorization). -/
theorem smooth_injective_of_support (hPs : ∀ q ∈ Ps, q.Prime) {b b' : ℕ → ℕ}
    (hb : ∀ q, q ∉ Ps → b q = 0) (hb' : ∀ q, q ∉ Ps → b' q = 0)
    (h : smooth Ps b = smooth Ps b') : b = b' := by
  funext r
  by_cases hr : r ∈ Ps
  · have := congrArg (fun n => n.factorization r) h
    simpa [factorization_smooth hPs, hr] using this
  · rw [hb r hr, hb' r hr]

theorem smooth_injOn_box (hPs : ∀ q ∈ Ps, q.Prime) (γ : ℕ → ℕ) :
    Set.InjOn (smooth Ps) (box Ps γ : Set (ℕ → ℕ)) := fun _ hb _ hb' h =>
  smooth_injective_of_support hPs (mem_box.1 hb).2 (mem_box.1 hb').2 h

/-- For primes `Ps`: `s(b) ∣ s(v) ↔ b ≤ v` on `Ps`. -/
theorem smooth_dvd_smooth_iff (hPs : ∀ q ∈ Ps, q.Prime) {b v : ℕ → ℕ} :
    smooth Ps b ∣ smooth Ps v ↔ ∀ q ∈ Ps, b q ≤ v q := by
  refine ⟨fun h q hq => ?_, smooth_dvd_smooth⟩
  have hpos : ∀ r ∈ Ps, 0 < r := fun r hr => (hPs r hr).pos
  have := (Nat.factorization_le_iff_dvd (smooth_ne_zero hpos b) (smooth_ne_zero hpos v)).2 h q
  simpa [factorization_smooth hPs, hq] using this

/-- The divisors of `s(v)` are exactly the `s(b)` for `b ∈ box Ps v` (i.e. `b ≤ v` on `Ps`,
`b = 0` off `Ps`). -/
theorem divisors_smooth (hPs : ∀ q ∈ Ps, q.Prime) (v : ℕ → ℕ) :
    (smooth Ps v).divisors = (box Ps v).image (smooth Ps) := by
  have hpos : ∀ r ∈ Ps, 0 < r := fun r hr => (hPs r hr).pos
  ext d
  rw [mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, hs⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hs (Nat.eq_zero_of_zero_dvd hd)
    have hle := (Nat.factorization_le_iff_dvd hd0 hs).2 hd
    refine ⟨fun q => if q ∈ Ps then d.factorization q else 0, ?_, ?_⟩
    · rw [mem_box]
      refine ⟨fun q hq => ?_, fun q hq => by simp [hq]⟩
      have := hle q
      simpa [hq, factorization_smooth hPs] using this
    · refine Nat.eq_of_factorization_eq (smooth_ne_zero hpos _) hd0 fun r => ?_
      rw [factorization_smooth hPs]
      by_cases hr : r ∈ Ps
      · simp [hr]
      · have := hle r
        simp only [factorization_smooth hPs, hr, ↓reduceIte, nonpos_iff_eq_zero] at this
        simp [hr, this]
  · rintro ⟨b, hb, rfl⟩
    exact ⟨smooth_dvd_smooth (mem_box.1 hb).1, smooth_ne_zero hpos v⟩

/-- Smooth numbers over disjoint sets of primes are coprime. -/
theorem coprime_smooth_of_disjoint {A B : Finset ℕ} (hAB : Disjoint A B)
    (hA : ∀ q ∈ A, q.Prime) (hB : ∀ q ∈ B, q.Prime) (v w : ℕ → ℕ) :
    Nat.Coprime (smooth A v) (smooth B w) := by
  unfold smooth
  rw [Nat.coprime_prod_left_iff]
  intro q hq
  rw [Nat.coprime_prod_right_iff]
  intro r hr
  apply Nat.Coprime.pow
  rw [Nat.coprime_primes (hA q hq) (hB r hr)]
  rintro rfl
  exact Finset.disjoint_left.1 hAB hq hr

/-- (vii) `E[τ(s)^θ] = Π_{q ∈ Ps} E_q[(v q + 1)^θ]` for every real `θ`. -/
theorem expect_tau_rpow (hPs : ∀ q ∈ Ps, q.Prime) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (θ : ℝ) :
    expect Ps ν γ (fun v => ((smooth Ps v).divisors.card : ℝ) ^ θ) =
      ∏ q ∈ Ps, expect1 q (ν q) (γ q) (fun a => ((a : ℝ) + 1) ^ θ) := by
  rw [← expect_prod]
  congr 1
  funext v
  rw [card_divisors_smooth_real hPs, Real.finsetProd_rpow _ _ (fun q _ => by positivity)]

/-- (vii) for natural exponents: `E[τ(s)^k] = Π_{q ∈ Ps} E_q[(v q + 1)^k]`. -/
theorem expect_tau_pow (hPs : ∀ q ∈ Ps, q.Prime) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (k : ℕ) :
    expect Ps ν γ (fun v => ((smooth Ps v).divisors.card : ℝ) ^ k) =
      ∏ q ∈ Ps, expect1 q (ν q) (γ q) (fun a => ((a : ℝ) + 1) ^ k) := by
  rw [← expect_prod]
  congr 1
  funext v
  rw [card_divisors_smooth_real hPs, prod_pow]

end MinModulus.Smooth
