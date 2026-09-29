import MinModulus.Tail2.Family
import MinModulus.Main.Main

/-!
# Tail2.Chain: the certificate chain with a general tail constant

STATUS: complete, no `sorry` (L2-T). Reuses `Main` (read-only): `hingeLoss_mono_cap`,
`hingeLoss_nonneg`, `one_le_tailFactor`, `tilt_mem`, `tilt_le_two`, `level_le_levelLoss`,
`levelLoss_le_hingeLoss`, `levelLoss_le_tail`, `budget`, `Arith.Setup`, `Distortion.criterion_kernel`.
Only `level_le_budget`, `sum_budget_lt`, `uncovered_of_cert`, `not_covers_of_cert` are restated for
`CertT` (their only change: the tail constant `C` and the tail field replace `100/(189 X)` and
`Tail.tail_bound_family_nu`).

## `CertT m X δ c T C`
`Main.Cert m X δ c T` without `two_pow_le`, with
* `tail`: `C` bounds `Σ_{p∈S} ∏_{q∈S,q<p}(1 + g q)/(p−1)^2` for every finite set `S` of primes `> X`
  (`g q = 2(3q−1)/(q−1)^2`), e.g. `C = 7051/(50000 X)` for `X ≥ 2·10^8` (`tail2_2e8`),
  `C = 12473/(100000 X)` for `X ≥ 10^9` (`tail2_1e9`), or the old `100/(189 X)` (`CertT.of_cert`);
* `total_lt : Σ_{p ≤ X} c p + T · C < 1`.

## Main results
* `not_covers_of_certT`: a `CertT m X δ c T C` (`2 ≤ m`) excludes coverings with distinct moduli `≥ m`.
* `CertT.of_cert`: every `Main.Cert` is a `CertT` with `C = 100/(189 X)`.
* `CertT.of_facts_2e8` / `of_facts_1e9` / `of_facts_2e9`: build a `CertT` from the fields of a `Cert` (minus `total_lt`)
  and the new total inequality `Σ c + T · C₀/X < 1` with the proved constants.
-/

namespace MinModulus.Tail2

open Finset MinModulus.Main

/-- **The numeric certificate with a general tail constant `C`.** -/
structure CertT (m X : ℕ) (δ : ℕ → ℝ) (c : ℕ → ℝ) (T C : ℝ) : Prop where
  delta_nonneg : ∀ p, p.Prime → 0 ≤ δ p
  delta_le_half : ∀ p, p.Prime → δ p ≤ 1 / 2
  delta_tail : ∀ p, p.Prime → X < p → δ p = 1 / 2
  loss_le : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ, hingeLoss m δ p (fun _ => N) ≤ c p
  prod_le : ∏ q ∈ Nat.primesLE X, tailFactor δ q ≤ T
  /-- `C` bounds the tail sums of every finite set of primes `> X`. -/
  tail : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ X < p) →
    ∑ p ∈ S, (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤ C
  total_lt : ∑ p ∈ Nat.primesLE X, c p + T * C < 1

theorem CertT.loss_le_all {m X : ℕ} {δ c : ℕ → ℝ} {T C : ℝ} (hc : CertT m X δ c T C) {p : ℕ}
    (hp : p.Prime) (hpX : p ≤ X) (γ : ℕ → ℕ) : hingeLoss m δ p γ ≤ c p :=
  (hingeLoss_mono_cap hc.delta_nonneg hc.delta_le_half hp fun _ hq =>
    le_sup (f := γ) hq).trans (hc.loss_le p hp hpX ((Nat.primesBelow p).sup γ))

theorem CertT.cost_nonneg {m X : ℕ} {δ c : ℕ → ℝ} {T C : ℝ} (hc : CertT m X δ c T C) {p : ℕ}
    (hp : p.Prime) (hpX : p ≤ X) : 0 ≤ c p :=
  (hingeLoss_nonneg hc.delta_nonneg hc.delta_le_half hp _).trans (hc.loss_le p hp hpX 0)

theorem CertT.T_nonneg {m X : ℕ} {δ c : ℕ → ℝ} {T C : ℝ} (hc : CertT m X δ c T C) : 0 ≤ T :=
  (prod_nonneg fun q hq => zero_le_one.trans (one_le_tailFactor
    (hc.delta_nonneg q (Nat.prime_of_mem_primesLE hq))
    (hc.delta_le_half q (Nat.prime_of_mem_primesLE hq))
    (Nat.prime_of_mem_primesLE hq).one_lt.le)).trans hc.prod_le

/-- Every `Main.Cert` is a `CertT` with the old constant `C = 100/(189 X)`. -/
theorem CertT.of_cert {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert m X δ c T) :
    CertT m X δ c T (100 / (189 * (X : ℝ))) where
  delta_nonneg := hc.delta_nonneg
  delta_le_half := hc.delta_le_half
  delta_tail := hc.delta_tail
  loss_le := hc.loss_le
  prod_le := hc.prod_le
  tail := fun S hS => Tail.tail_bound_g X hc.two_pow_le S hS
  total_lt := hc.total_lt

section Levels

variable {ι : Type*} [Fintype ι] (S : Arith.Setup ι)

theorem level_le_budgetT {X : ℕ} {δ c : ℕ → ℝ} {T C : ℝ} (hc : CertT S.m X δ c T C)
    (ℓ : Fin S.n) :
    ∑ x, (∏ j, Distortion.kernel S.B (δL S δ) ℓ j x (x j)) *
        (max 0 (∑ i, (if ∀ j, x j ∈ S.rect ℓ i j then S.wt ℓ i else 0) - δL S δ ℓ) /
          (1 - δL S δ ℓ))
      ≤ budget S X δ c T ℓ := by
  refine (level_le_levelLoss S δ hc.delta_nonneg hc.delta_le_half ℓ).trans ?_
  unfold budget
  split_ifs with h
  · exact (levelLoss_le_hingeLoss S δ hc.delta_nonneg hc.delta_le_half ℓ).trans
      (hc.loss_le_all (S.p_prime ℓ) h (capN S))
  · exact levelLoss_le_tail S hc.delta_nonneg hc.delta_le_half hc.delta_tail hc.prod_le ℓ
      (not_le.1 h)

theorem sum_budget_ltT {X : ℕ} {δ c : ℕ → ℝ} {T C : ℝ} (hc : CertT S.m X δ c T C) :
    ∑ ℓ : Fin S.n, budget S X δ c T ℓ < 1 := by
  unfold budget
  rw [sum_ite]
  have h1 : ∑ ℓ ∈ univ.filter (fun ℓ => S.p ℓ ≤ X), c (S.p ℓ) ≤
      ∑ p ∈ Nat.primesLE X, c p := by
    rw [← sum_image fun a _ b _ h => S.p_injective h]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ =>
      hc.cost_nonneg (Nat.prime_of_mem_primesLE hq) (Nat.mem_primesLE.1 hq).1
    intro q hq
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hq
    exact Nat.mem_primesLE.2 ⟨(mem_filter.1 hj).2, S.p_prime j⟩
  have h2 : ∑ ℓ ∈ univ.filter (fun ℓ => ¬ S.p ℓ ≤ X),
      T * (∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j)) / ((S.p ℓ : ℝ) - 1) ^ 2 ≤
      T * C := by
    simp_rw [mul_div_assoc]
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hc.T_nonneg
    exact family_of_finset hc.tail (tailSet S X) S.p
      (S.p_strictMono.strictMonoOn _)
      (fun i hi => ⟨S.p_prime i, not_le.1 (mem_filter.1 hi).2⟩)
      (fun j => tilt δ (S.p j))
      (fun i _ => (tilt_mem hc.delta_nonneg hc.delta_le_half (S.p_prime i)).1)
      (fun i _ => tilt_le_two (hc.delta_le_half _ (S.p_prime i)))
  linarith [hc.total_lt]

/-- **The chain with a general tail constant**: a `CertT` for `S.m` leaves an integer uncovered. -/
theorem uncovered_of_certT {X : ℕ} {δ c : ℕ → ℝ} {T C : ℝ} (hc : CertT S.m X δ c T C) :
    ∃ x : ℤ, ∀ i, ¬ ((S.d i : ℤ) ∣ x - S.a i) := by
  have hL0 : ∀ ℓ, 0 ≤ δL S δ ℓ := fun ℓ => hc.delta_nonneg _ (S.p_prime ℓ)
  have hL1 : ∀ ℓ, δL S δ ℓ < 1 := fun ℓ =>
    (hc.delta_le_half _ (S.p_prime ℓ)).trans_lt (by norm_num)
  obtain ⟨y, hy⟩ := Distortion.criterion_kernel (B := S.B) (δ := δL S δ) S.B_congr hL0 hL1
    (fun ℓ x => max 0 (∑ i, (if ∀ j, x j ∈ S.rect ℓ i j then S.wt ℓ i else 0) - δL S δ ℓ) /
      (1 - δL S δ ℓ))
    (fun ℓ x => S.hinge_alpha_le ℓ x le_rfl (hL1 ℓ))
    (lt_of_le_of_lt (sum_le_sum fun ℓ _ => level_le_budgetT S hc ℓ) (sum_budget_ltT S hc))
  exact S.exists_int_of_forall_not_mem_B y hy

end Levels

/-- **Main theorem, general tail constant.** If `CertT m X δ c T C` holds (`2 ≤ m`), no system of
congruences with distinct moduli `≥ m` covers `ℤ`. -/
theorem not_covers_of_certT {m X : ℕ} {δ c : ℕ → ℝ} {T C : ℝ} (hc : CertT m X δ c T C)
    (hm : 2 ≤ m) {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ) (hd : Function.Injective d)
    (hdm : ∀ i, m ≤ d i) : ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  uncovered_of_certT (⟨m, d, a, hm, hd, hdm⟩ : Arith.Setup ι) hc

/-- Build a `CertT` with the proved constant at `X ≥ 2·10^8`. -/
theorem CertT.of_facts_2e8 {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hX : 2 * 10 ^ 8 ≤ X)
    (h0 : ∀ p, p.Prime → 0 ≤ δ p) (h1 : ∀ p, p.Prime → δ p ≤ 1 / 2)
    (htail : ∀ p, p.Prime → X < p → δ p = 1 / 2)
    (hloss : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ, hingeLoss m δ p (fun _ => N) ≤ c p)
    (hprod : ∏ q ∈ Nat.primesLE X, tailFactor δ q ≤ T)
    (htot : ∑ p ∈ Nat.primesLE X, c p + T * (7051 / 50000 / (X : ℝ)) < 1) :
    CertT m X δ c T (7051 / 50000 / (X : ℝ)) :=
  ⟨h0, h1, htail, hloss, hprod, fun S hS => tail2_2e8 hX S hS, htot⟩

/-- Build a `CertT` with the proved constant at `X ≥ 10^9`. -/
theorem CertT.of_facts_1e9 {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hX : 10 ^ 9 ≤ X)
    (h0 : ∀ p, p.Prime → 0 ≤ δ p) (h1 : ∀ p, p.Prime → δ p ≤ 1 / 2)
    (htail : ∀ p, p.Prime → X < p → δ p = 1 / 2)
    (hloss : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ, hingeLoss m δ p (fun _ => N) ≤ c p)
    (hprod : ∏ q ∈ Nat.primesLE X, tailFactor δ q ≤ T)
    (htot : ∑ p ∈ Nat.primesLE X, c p + T * (12473 / 100000 / (X : ℝ)) < 1) :
    CertT m X δ c T (12473 / 100000 / (X : ℝ)) :=
  ⟨h0, h1, htail, hloss, hprod, fun S hS => tail2_1e9 hX S hS, htot⟩

/-- Build a `CertT` with the proved constant at `X ≥ 2·10^9`. -/
theorem CertT.of_facts_2e9 {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hX : 2 * 10 ^ 9 ≤ X)
    (h0 : ∀ p, p.Prime → 0 ≤ δ p) (h1 : ∀ p, p.Prime → δ p ≤ 1 / 2)
    (htail : ∀ p, p.Prime → X < p → δ p = 1 / 2)
    (hloss : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ, hingeLoss m δ p (fun _ => N) ≤ c p)
    (hprod : ∏ q ∈ Nat.primesLE X, tailFactor δ q ≤ T)
    (htot : ∑ p ∈ Nat.primesLE X, c p + T * (5941 / 50000 / (X : ℝ)) < 1) :
    CertT m X δ c T (5941 / 50000 / (X : ℝ)) :=
  ⟨h0, h1, htail, hloss, hprod, fun S hS => tail2_2e9 hX S hS, htot⟩

end MinModulus.Tail2
