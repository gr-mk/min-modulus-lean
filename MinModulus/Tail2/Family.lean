import MinModulus.Tail2.Numerics

/-!
# Tail2.Family: the sharper tail in the shape of `Tail.tail_bound_family_nu`

STATUS: complete, no `sorry` (L2-T).

`family_of_finset`: any bound `C` for the finset sums `Σ_{p∈S} ∏_{q∈S,q<p}(1 + g q)/(p−1)^2`
(`S` a finite set of primes `> X`) also bounds the family sums with tilts `0 ≤ ν ≤ 2`, i.e. the
exact shape used by `Main.sum_budget_lt`:
`Σ_{i∈s} ∏_{j∈s, j<i} (1 + ν_j (3P_j − 1)/(P_j − 1)^2) / (P_i − 1)^2 ≤ C`.

Corollaries (same hypotheses as `Tail.tail_bound_family_nu`, except `X ≥ 2·10^8` resp. `X ≥ 10^9`
instead of `X ≥ 2^27`):
* `tail_bound_family_nu_2e8 : … ≤ 7051 / 50000 / X` (`0.14102/X`; old `100/(189 X) = 0.52910/X`);
* `tail_bound_family_nu_1e9 : … ≤ 12473 / 100000 / X` (`0.12473/X`);
* `tail_bound_family_nu_2e9 : … ≤ 5941 / 50000 / X` (`0.11882/X`, `X ≥ 2·10^9`).
-/

namespace MinModulus.Tail2

open Finset

/-- A finset tail bound gives the family tail bound with tilts `0 ≤ ν ≤ 2`. -/
theorem family_of_finset {X : ℕ} {C : ℝ}
    (hC : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ X < p) →
      ∑ p ∈ S, (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 ≤ C)
    {ι : Type*} [LinearOrder ι] (s : Finset ι) (P : ι → ℕ) (hP : StrictMonoOn P s)
    (hS : ∀ i ∈ s, (P i).Prime ∧ X < P i) (ν : ι → ℝ) (hν0 : ∀ i ∈ s, 0 ≤ ν i)
    (hν2 : ∀ i ∈ s, ν i ≤ 2) :
    ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)) /
      ((P i : ℝ) - 1) ^ 2 ≤ C := by
  have hinj : Set.InjOn P s := hP.injOn
  have hSimg : ∀ p ∈ s.image P, p.Prime ∧ X < p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hp
    exact hS i hi
  have hbase : ∀ i ∈ s, 0 ≤ (3 * (P i : ℝ) - 1) / ((P i : ℝ) - 1) ^ 2 := by
    intro i hi
    have : (1 : ℝ) ≤ P i := by exact_mod_cast (hS i hi).1.one_lt.le
    exact div_nonneg (by linarith) (sq_nonneg _)
  have key : ∀ i ∈ s, ∏ j ∈ s with j < i, (1 + gR (P j)) =
      ∏ q ∈ s.image P with q < P i, (1 + gR q) := by
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
  calc ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)) /
        ((P i : ℝ) - 1) ^ 2
      ≤ ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + gR (P j))) / ((P i : ℝ) - 1) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply Finset.prod_le_prod₀
        · intro j hj
          have hj' := (mem_filter.1 hj).1
          have := mul_nonneg (hν0 j hj') (hbase j hj')
          rw [mul_div_assoc]
          linarith
        · intro j hj
          have hj' := (mem_filter.1 hj).1
          have := mul_le_mul_of_nonneg_right (hν2 j hj') (hbase j hj')
          unfold gR
          rw [mul_div_assoc, mul_div_assoc]
          linarith
    _ = ∑ i ∈ s, (∏ q ∈ s.image P with q < P i, (1 + gR q)) / ((P i : ℝ) - 1) ^ 2 := by
        apply Finset.sum_congr rfl; intro i hi; rw [key i hi]
    _ = ∑ p ∈ s.image P, (∏ q ∈ s.image P with q < p, (1 + gR q)) / ((p : ℝ) - 1) ^ 2 := by
        rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
    _ ≤ C := hC _ hSimg

/-- **Sharper tail, family form, `X ≥ 2·10^8`**: constant `7051/50000 = 0.14102`. -/
theorem tail_bound_family_nu_2e8 {ι : Type*} [LinearOrder ι] (X : ℕ) (hX : 2 * 10 ^ 8 ≤ X)
    (s : Finset ι) (P : ι → ℕ) (hP : StrictMonoOn P s)
    (hS : ∀ i ∈ s, (P i).Prime ∧ X < P i) (ν : ι → ℝ) (hν0 : ∀ i ∈ s, 0 ≤ ν i)
    (hν2 : ∀ i ∈ s, ν i ≤ 2) :
    ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)) /
      ((P i : ℝ) - 1) ^ 2 ≤ 7051 / 50000 / (X : ℝ) :=
  family_of_finset (fun S hS => tail2_2e8 hX S hS) s P hP hS ν hν0 hν2

/-- **Sharper tail, family form, `X ≥ 10^9`**: constant `12473/100000 = 0.12473`. -/
theorem tail_bound_family_nu_1e9 {ι : Type*} [LinearOrder ι] (X : ℕ) (hX : 10 ^ 9 ≤ X)
    (s : Finset ι) (P : ι → ℕ) (hP : StrictMonoOn P s)
    (hS : ∀ i ∈ s, (P i).Prime ∧ X < P i) (ν : ι → ℝ) (hν0 : ∀ i ∈ s, 0 ≤ ν i)
    (hν2 : ∀ i ∈ s, ν i ≤ 2) :
    ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)) /
      ((P i : ℝ) - 1) ^ 2 ≤ 12473 / 100000 / (X : ℝ) :=
  family_of_finset (fun S hS => tail2_1e9 hX S hS) s P hP hS ν hν0 hν2

/-- **Sharper tail, family form, `X ≥ 2·10^9`**: constant `5941/50000 = 0.11882`. -/
theorem tail_bound_family_nu_2e9 {ι : Type*} [LinearOrder ι] (X : ℕ) (hX : 2 * 10 ^ 9 ≤ X)
    (s : Finset ι) (P : ι → ℕ) (hP : StrictMonoOn P s)
    (hS : ∀ i ∈ s, (P i).Prime ∧ X < P i) (ν : ι → ℝ) (hν0 : ∀ i ∈ s, 0 ≤ ν i)
    (hν2 : ∀ i ∈ s, ν i ≤ 2) :
    ∑ i ∈ s, (∏ j ∈ s with j < i, (1 + ν j * (3 * (P j : ℝ) - 1) / ((P j : ℝ) - 1) ^ 2)) /
      ((P i : ℝ) - 1) ^ 2 ≤ 5941 / 50000 / (X : ℝ) :=
  family_of_finset (fun S hS => tail2_2e9 hX S hS) s P hP hS ν hν0 hν2

end MinModulus.Tail2
