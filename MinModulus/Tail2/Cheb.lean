import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Tail2.Cheb: Chebyshev bounds for the primes in `(X, N]`, with a leftover

STATUS: complete, no `sorry` (L2-T). Imports only Mathlib.

## Main result
`thetaIoc_le`: for naturals `10^8 ≤ X ≤ N`,
`θ(X, N] := Σ_{X < q ≤ N, q prime} log q ≤ 2 (log 2 + 10^-6) (N − X) + log(4/3) · X`.

## Proof
* Leftover (`X ≤ N ≤ 2X`): the primes of `(X, N]` divide `C(N, X)` and `C(N, X) · 3^X ≤ 4^N` (binomial
  theorem for `(3 + 1)^N`), so `θ(X, N] ≤ N log 4 − X log 3 = 2 log 2 (N − X) + X log(4/3)`.
* Dyadic step (`N > 2X`, `M = N / 2 ≥ X`): the primes of `(M, N]` have product `≤ N · 4^M`
  (`C(2M, M) ≤ 4^M`, `C(2M+1, M) ≤ 4^M`, plus the possible prime `M + 1`), so
  `θ(M, N] ≤ N log 2 + log N ≤ (log 2 + 10^-6) N`; strong induction on `N`.
-/

namespace MinModulus.Tail2

open Finset Real

/-- The θ-mass of the primes in `(A, B]`: `Σ_{A < q ≤ B, q prime} log q`. -/
noncomputable def thetaIoc (A B : ℕ) : ℝ := ∑ q ∈ Ioc A B, if q.Prime then Real.log q else 0

/-- The product of the primes in `(A, B]`. -/
def primeProd (A B : ℕ) : ℕ := ∏ q ∈ (Ioc A B).filter Nat.Prime, q

theorem primeProd_pos (A B : ℕ) : 0 < primeProd A B :=
  Finset.prod_pos fun _ hq => (mem_filter.1 hq).2.pos

theorem thetaIoc_eq_log (A B : ℕ) : thetaIoc A B = Real.log (primeProd A B) := by
  unfold thetaIoc primeProd
  rw [← Finset.sum_filter, Nat.cast_prod, Real.log_prod]
  intro q hq
  have := (mem_filter.1 hq).2.pos
  positivity

theorem thetaIoc_nonneg (A B : ℕ) : 0 ≤ thetaIoc A B := by
  unfold thetaIoc
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_rfl

theorem thetaIoc_self (A : ℕ) : thetaIoc A A = 0 := by simp [thetaIoc]

theorem thetaIoc_add {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) :
    thetaIoc A B + thetaIoc B C = thetaIoc A C := by
  unfold thetaIoc
  exact Finset.sum_Ioc_consecutive _ hAB hBC

theorem thetaIoc_succ {A N : ℕ} (h : A ≤ N) :
    thetaIoc A (N + 1) = thetaIoc A N + if (N + 1).Prime then Real.log (N + 1 : ℕ) else 0 := by
  unfold thetaIoc
  rw [Finset.sum_Ioc_succ_top h]

/-! ### Divisibility of binomial coefficients -/

/-- For `X ≤ N ≤ 2X`, the product of the primes of `(X, N]` divides `C(N, X)`. -/
theorem primeProd_dvd_choose {X N : ℕ} (hXN : X ≤ N) (hN : N ≤ 2 * X) :
    primeProd X N ∣ N.choose X := by
  unfold primeProd
  apply Finset.prod_primes_dvd
  · intro q hq
    exact (mem_filter.1 hq).2.prime
  · intro q hq
    obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
    rw [mem_Ioc] at hq1
    have hN' : N = X + (N - X) := by omega
    have := hq2.dvd_choose_add (a := X) (b := N - X) hq1.1 (by omega) (by omega)
    rwa [← hN'] at this

/-- `C(N, X) · 3^X ≤ 4^N` (one term of the binomial expansion of `(3 + 1)^N`). -/
theorem choose_mul_three_pow_le {X N : ℕ} (h : X ≤ N) : N.choose X * 3 ^ X ≤ 4 ^ N := by
  have hexp := add_pow (3 : ℕ) 1 N
  have hmem : X ∈ range (N + 1) := mem_range.2 (by omega)
  calc N.choose X * 3 ^ X = 3 ^ X * 1 ^ (N - X) * N.choose X := by ring
    _ ≤ ∑ m ∈ range (N + 1), 3 ^ m * 1 ^ (N - m) * N.choose m :=
        Finset.single_le_sum (f := fun m => 3 ^ m * 1 ^ (N - m) * N.choose m)
          (fun _ _ => Nat.zero_le _) hmem
    _ = (3 + 1) ^ N := hexp.symm
    _ = 4 ^ N := by norm_num

/-- Leftover piece: `primeProd X N · 3^X ≤ 4^N` for `X ≤ N ≤ 2X`. -/
theorem primeProd_mul_three_pow_le {X N : ℕ} (hXN : X ≤ N) (hN : N ≤ 2 * X) :
    primeProd X N * 3 ^ X ≤ 4 ^ N := by
  have hpos : 0 < N.choose X := Nat.choose_pos hXN
  calc primeProd X N * 3 ^ X ≤ N.choose X * 3 ^ X :=
        Nat.mul_le_mul_right _ (Nat.le_of_dvd hpos (primeProd_dvd_choose hXN hN))
    _ ≤ 4 ^ N := choose_mul_three_pow_le hXN

/-- Leftover piece in log form: `θ(X, N] ≤ 2 log 2 (N − X) + log(4/3) X` for `X ≤ N ≤ 2X`. -/
theorem thetaIoc_le_leftover {X N : ℕ} (hXN : X ≤ N) (hN : N ≤ 2 * X) :
    thetaIoc X N ≤ 2 * Real.log 2 * ((N : ℝ) - X) + Real.log (4 / 3) * X := by
  have h := primeProd_mul_three_pow_le hXN hN
  have h' : ((primeProd X N : ℕ) : ℝ) * (3 : ℝ) ^ X ≤ (4 : ℝ) ^ N := by exact_mod_cast h
  have hpos : (0 : ℝ) < (primeProd X N : ℕ) := by exact_mod_cast primeProd_pos X N
  have hlog := Real.log_le_log (by positivity) h'
  rw [Real.log_mul hpos.ne' (by positivity), Real.log_pow, Real.log_pow] at hlog
  rw [thetaIoc_eq_log]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h43 : Real.log (4 / 3) = Real.log 4 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  rw [h4] at hlog
  rw [h43, h4]
  linarith

/-- Dyadic piece: the primes of `(N/2, N]` have product `≤ N · 4^(N/2)` (for `N ≥ 1`). -/
theorem primeProd_half_le {N : ℕ} (hN : 1 ≤ N) : primeProd (N / 2) N ≤ N * 4 ^ (N / 2) := by
  set M := N / 2 with hM
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- N = 2M
    have hNM : N = 2 * M := by omega
    have h1 : primeProd M N ≤ N.choose M :=
      Nat.le_of_dvd (Nat.choose_pos (by omega)) (primeProd_dvd_choose (by omega) (by omega))
    have h2 : N.choose M ≤ 4 ^ M := by
      rw [hNM, ← Nat.centralBinom_eq_two_mul_choose]
      exact Nat.centralBinom_le_four_pow M
    calc primeProd M N ≤ 4 ^ M := h1.trans h2
      _ ≤ N * 4 ^ M := Nat.le_mul_of_pos_left _ hN
  · -- N = 2M + 1
    have hNM : N = 2 * M + 1 := by omega
    have hsplit : primeProd M N = primeProd M (M + 1) * primeProd (M + 1) N := by
      unfold primeProd
      rw [← Finset.prod_union]
      · congr 1
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
      · exact Finset.disjoint_filter_filter (Finset.disjoint_left.2 fun x hx h'x =>
            lt_irrefl _ ((mem_Ioc.1 h'x).1.trans_le (mem_Ioc.1 hx).2))
    have h1 : primeProd M (M + 1) ≤ M + 1 := by
      unfold primeProd
      have hsub : (Ioc M (M + 1)).filter Nat.Prime ⊆ {M + 1} := by
        intro x hx
        rw [mem_filter, mem_Ioc] at hx
        rw [mem_singleton]
        omega
      calc ∏ q ∈ (Ioc M (M + 1)).filter Nat.Prime, q ≤ ∏ q ∈ ({M + 1} : Finset ℕ), q :=
            Finset.prod_le_prod_of_subset_of_one_le hsub fun i hi _ => by
              rw [mem_singleton] at hi; omega
        _ = M + 1 := prod_singleton _ _
    have h2 : primeProd (M + 1) N ≤ 4 ^ M := by
      have hd := primeProd_dvd_choose (X := M + 1) (N := N) (by omega) (by omega)
      have hc : N.choose (M + 1) = (2 * M + 1).choose M := by
        rw [hNM, Nat.choose_symm_of_eq_add]
        omega
      calc primeProd (M + 1) N ≤ N.choose (M + 1) :=
            Nat.le_of_dvd (Nat.choose_pos (by omega)) hd
        _ = (2 * M + 1).choose M := hc
        _ ≤ 4 ^ M := Nat.choose_middle_le_pow M
    rw [hsplit]
    calc primeProd M (M + 1) * primeProd (M + 1) N ≤ (M + 1) * 4 ^ M :=
          Nat.mul_le_mul h1 h2
      _ ≤ N * 4 ^ M := Nat.mul_le_mul_right _ (by omega)

/-- `log N ≤ N / 10^6` for `N ≥ 10^8`. -/
theorem log_le_div_million {N : ℝ} (hN : 10 ^ 8 ≤ N) : Real.log N ≤ N / 10 ^ 6 := by
  have hN0 : 0 < N := by linarith
  set x := N / 10 ^ 6 with hx
  have hx100 : (100 : ℝ) ≤ x := by rw [hx, le_div_iff₀ (by norm_num)]; linarith
  have hexp := Real.pow_div_factorial_le_exp (x := x) (by linarith) 6
  have hfac : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hfac] at hexp
  have hx5 : (10 : ℝ) ^ 10 ≤ x ^ 5 := by
    calc (10 : ℝ) ^ 10 = 100 ^ 5 := by norm_num
      _ ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx100 5
  have hNx : N = 10 ^ 6 * x := by rw [hx]; field_simp
  have key : N ≤ x ^ 6 / 720 := by
    rw [hNx, le_div_iff₀ (by norm_num)]
    have : x ^ 6 = x * x ^ 5 := by ring
    rw [this]
    nlinarith
  rw [Real.log_le_iff_le_exp hN0]
  linarith

/-- Dyadic piece in log form: `θ(N/2, N] ≤ (log 2 + 10^-6) N` for `N ≥ 10^8`. -/
theorem thetaIoc_half_le {N : ℕ} (hN : 10 ^ 8 ≤ N) :
    thetaIoc (N / 2) N ≤ (Real.log 2 + 1 / 10 ^ 6) * N := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have h := primeProd_half_le hN1
  have h' : ((primeProd (N / 2) N : ℕ) : ℝ) ≤ (N : ℝ) * (4 : ℝ) ^ (N / 2) := by exact_mod_cast h
  have hpos : (0 : ℝ) < (primeProd (N / 2) N : ℕ) := by exact_mod_cast primeProd_pos _ _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlog := Real.log_le_log hpos h'
  rw [Real.log_mul hNpos.ne' (by positivity), Real.log_pow] at hlog
  rw [thetaIoc_eq_log]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hhalf : ((N / 2 : ℕ) : ℝ) * 2 ≤ N := by
    have : N / 2 * 2 ≤ N := Nat.div_mul_le_self N 2
    exact_mod_cast this
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : Real.log N ≤ N / 10 ^ 6 := log_le_div_million (by exact_mod_cast hN)
  rw [h4] at hlog
  nlinarith

/-- **Chebyshev with a leftover.** For `10^8 ≤ X ≤ N`:
`θ(X, N] ≤ 2 (log 2 + 10^-6) (N − X) + log(4/3) · X`. -/
theorem thetaIoc_le {X : ℕ} (hX : 10 ^ 8 ≤ X) :
    ∀ N, X ≤ N → thetaIoc X N ≤ 2 * (Real.log 2 + 1 / 10 ^ 6) * ((N : ℝ) - X) +
      Real.log (4 / 3) * X := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hXN
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_cases hN : N ≤ 2 * X
    · have h := thetaIoc_le_leftover hXN hN
      have : (0 : ℝ) ≤ (N : ℝ) - X := by
        have : (X : ℝ) ≤ N := by exact_mod_cast hXN
        linarith
      nlinarith
    · push Not at hN
      set M := N / 2 with hM
      have hXM : X ≤ M := by omega
      have hMN : M < N := by omega
      have hIH := ih M hMN hXM
      have hsplit := thetaIoc_add hXM hMN.le
      have hN8 : 10 ^ 8 ≤ N := by omega
      have hhalf := thetaIoc_half_le hN8
      have hM2 : (M : ℝ) * 2 ≤ N := by
        have : M * 2 ≤ N := Nat.div_mul_le_self N 2
        exact_mod_cast this
      rw [← hsplit]
      nlinarith

end MinModulus.Tail2
