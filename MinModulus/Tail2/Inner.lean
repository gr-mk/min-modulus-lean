import MinModulus.Tail2.Cheb

/-!
# Tail2.Inner: `Σ_{X < q ≤ N} g(q)` via an Abel invariant over the integers

STATUS: complete, no `sorry` (L2-T). Imports `Tail2.Cheb` (Mathlib only).

## Main result
`inner_bound`: for naturals `10^8 ≤ X ≤ N`, with `g s = 2(3s−1)/(s−1)^2`,
`Σ_{X < q ≤ N, q prime} g q ≤ 2 cA KK (log log N − log log X) + EE KK / log X`,
where `cA = log 2 + 10^-6`, `KK = 6 (1 + 10^-7)`, `EE = log(4/3)`.

## Proof
With `ψ s = g s / log s` (antitone) and `Θ N = 2 cA (N − X) + EE X ≥ θ(X, N]` (`Cheb.thetaIoc_le`):
the invariant `Σ_{X<q≤N} g q + ψ N (Θ N − θ(X, N]) ≤ 2 cA Σ_{X<n≤N} ψ n + ψ X · EE X` holds at `N = X`
and is preserved from `N` to `N + 1` (the new prime term `ψ(N+1) log(N+1)` cancels, and
`ψ(N+1) ≤ ψ N`). Then `ψ n ≤ KK / (n log n) ≤ KK (log log n − log log (n−1))` and `X ψ X ≤ KK/log X`.
No sorting of the primes is needed.
-/

namespace MinModulus.Tail2

open Finset Real

/-- `g s = 2(3s−1)/(s−1)^2`: the tail factor `ν (3s−1)/(s−1)^2` for the tilt `ν = 2`. -/
noncomputable def gR (s : ℝ) : ℝ := 2 * (3 * s - 1) / (s - 1) ^ 2

/-- `ψ s = g s / log s`. -/
noncomputable def psiR (s : ℝ) : ℝ := gR s / Real.log s

/-- The Chebyshev constant of the dyadic pieces: `log 2 + 10^-6`. -/
noncomputable def cA : ℝ := Real.log 2 + 1 / 10 ^ 6

/-- `KK = 6 (1 + 10^-7) ≥ s g(s)` for `s ≥ 10^8`. -/
noncomputable def KK : ℝ := 6 * (1 + 1 / 10 ^ 7)

/-- The leftover constant `log(4/3)`. -/
noncomputable def EE : ℝ := Real.log (4 / 3)

theorem cA_pos : 0 < cA := by
  unfold cA; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity

theorem KK_pos : 0 < KK := by unfold KK; positivity

theorem EE_pos : 0 < EE := Real.log_pos (by norm_num)

theorem gR_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ gR s := by
  unfold gR
  apply div_nonneg _ (sq_nonneg _)
  linarith

theorem gR_anti {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : gR t ≤ gR s := by
  unfold gR
  have ha : 0 < s - 1 := by linarith
  have hb : 0 < t - 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hab : s - 1 ≤ t - 1 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hab ha.le, mul_le_mul hab hab ha.le hb.le,
    mul_nonneg ha.le hb.le, mul_nonneg (mul_nonneg ha.le hb.le) (sub_nonneg.2 hab)]

theorem psiR_nonneg {s : ℝ} (hs : 1 < s) : 0 ≤ psiR s := by
  unfold psiR
  exact div_nonneg (gR_nonneg hs.le) (Real.log_pos hs).le

theorem psiR_anti {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) : psiR t ≤ psiR s := by
  unfold psiR
  have hls : 0 < Real.log s := Real.log_pos hs
  have hlt : Real.log s ≤ Real.log t := Real.log_le_log (by linarith) hst
  calc gR t / Real.log t ≤ gR s / Real.log t :=
        div_le_div_of_nonneg_right (gR_anti hs hst) (hls.trans_le hlt).le
    _ ≤ gR s / Real.log s := div_le_div_of_nonneg_left (gR_nonneg hs.le) hls hlt

/-- `s g(s) ≤ KK` for `s ≥ 10^8`. -/
theorem mul_gR_le {s : ℝ} (hs : 10 ^ 8 ≤ s) : s * gR s ≤ KK := by
  unfold gR KK
  have h1 : 0 < s - 1 := by linarith
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

theorem gR_le {s : ℝ} (hs : 10 ^ 8 ≤ s) : gR s ≤ KK / s := by
  have hs0 : 0 < s := by linarith
  rw [le_div_iff₀ hs0, mul_comm]
  exact mul_gR_le hs

/-- `ψ n ≤ KK / (n log n)` for `n ≥ 10^8`. -/
theorem psiR_le {s : ℝ} (hs : 10 ^ 8 ≤ s) : psiR s ≤ KK / (s * Real.log s) := by
  have hs0 : 0 < s := by linarith
  have hl : 0 < Real.log s := Real.log_pos (by linarith)
  unfold psiR
  rw [div_le_div_iff₀ hl (by positivity)]
  have := gR_le hs
  rw [le_div_iff₀ hs0] at this
  nlinarith

/-- `1/(n log n) ≤ log log n − log log (n−1)` for `n ≥ 3`. -/
theorem inv_mul_log_le {n : ℝ} (hn : 3 ≤ n) :
    1 / (n * Real.log n) ≤ Real.log (Real.log n) - Real.log (Real.log (n - 1)) := by
  have hn1 : 0 < n - 1 := by linarith
  have ha : 0 < Real.log (n - 1) := Real.log_pos (by linarith)
  have hb : 0 < Real.log n := Real.log_pos (by linarith)
  have hab : Real.log (n - 1) < Real.log n := Real.log_lt_log hn1 (by linarith)
  -- log n − log (n−1) ≥ 1/n
  have h1 : 1 / n ≤ Real.log n - Real.log (n - 1) := by
    have := Real.one_sub_inv_le_log_of_pos (x := n / (n - 1)) (by positivity)
    rw [Real.log_div (by linarith) hn1.ne', inv_div] at this
    have e : 1 - (n - 1) / n = 1 / n := by field_simp; ring
    linarith
  -- log log n − log log (n−1) ≥ 1 − log(n−1)/log n
  have h2 : 1 - Real.log (n - 1) / Real.log n ≤
      Real.log (Real.log n) - Real.log (Real.log (n - 1)) := by
    have := Real.one_sub_inv_le_log_of_pos (x := Real.log n / Real.log (n - 1)) (by positivity)
    rw [Real.log_div hb.ne' ha.ne', inv_div] at this
    exact this
  have e2 : 1 - Real.log (n - 1) / Real.log n = (Real.log n - Real.log (n - 1)) / Real.log n := by
    field_simp
  rw [e2] at h2
  refine le_trans ?_ h2
  rw [div_le_div_iff₀ (by positivity) hb]
  have hn0 : 0 < n := by linarith
  rw [div_le_iff₀ hn0] at h1
  nlinarith

/-- The Abel invariant. -/
theorem inner_inv {X : ℕ} (hX : 10 ^ 8 ≤ X) : ∀ N, X ≤ N →
    (∑ q ∈ Ioc X N, if q.Prime then gR q else 0) +
        psiR N * (2 * cA * ((N : ℝ) - X) + EE * X - thetaIoc X N)
      ≤ 2 * cA * (∑ n ∈ Ioc X N, psiR n) + psiR X * (EE * X) := by
  intro N hXN
  induction N, hXN using Nat.le_induction with
  | base => simp [thetaIoc_self]
  | succ N hXN ih =>
    have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
    have hXNr : (X : ℝ) ≤ N := by exact_mod_cast hXN
    have hN1 : (1 : ℝ) < N := by linarith
    have hD := thetaIoc_le hX N hXN
    have hanti : psiR ((N : ℝ) + 1) ≤ psiR N := psiR_anti hN1 (by linarith)
    have hpsi1 : 0 ≤ psiR ((N : ℝ) + 1) := psiR_nonneg (by linarith)
    rw [Finset.sum_Ioc_succ_top hXN, Finset.sum_Ioc_succ_top hXN, thetaIoc_succ hXN]
    push_cast
    have hcancel : (if (N + 1).Prime then gR ((N : ℝ) + 1) else 0) -
        psiR ((N : ℝ) + 1) * (if (N + 1).Prime then Real.log ((N : ℝ) + 1) else 0) = 0 := by
      split_ifs
      · unfold psiR
        have : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
        field_simp
        ring
      · ring
    have hDnn : 0 ≤ 2 * cA * ((N : ℝ) - X) + EE * X - thetaIoc X N := by
      unfold cA at hD ⊢; unfold EE; linarith
    have hmono : psiR ((N : ℝ) + 1) * (2 * cA * ((N : ℝ) - X) + EE * X - thetaIoc X N) ≤
        psiR N * (2 * cA * ((N : ℝ) - X) + EE * X - thetaIoc X N) :=
      mul_le_mul_of_nonneg_right hanti hDnn
    nlinarith

/-- `Σ_{X<q≤N} g q ≤ 2 cA Σ_{X<n≤N} ψ n + ψ X · EE X`. -/
theorem sum_g_le {X : ℕ} (hX : 10 ^ 8 ≤ X) {N : ℕ} (hXN : X ≤ N) :
    (∑ q ∈ Ioc X N, if q.Prime then gR q else 0) ≤
      2 * cA * (∑ n ∈ Ioc X N, psiR n) + psiR X * (EE * X) := by
  have h := inner_inv hX N hXN
  have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
  have hXNr : (X : ℝ) ≤ N := by exact_mod_cast hXN
  have hD := thetaIoc_le hX N hXN
  have hDnn : 0 ≤ 2 * cA * ((N : ℝ) - X) + EE * X - thetaIoc X N := by
    unfold cA at hD ⊢; unfold EE; linarith
  have hp : 0 ≤ psiR N := psiR_nonneg (by linarith)
  nlinarith [mul_nonneg hp hDnn]

/-- `Σ_{X<n≤N} ψ n ≤ KK (log log N − log log X)`. -/
theorem sum_psi_le {X : ℕ} (hX : 10 ^ 8 ≤ X) : ∀ N, X ≤ N →
    ∑ n ∈ Ioc X N, psiR n ≤ KK * (Real.log (Real.log N) - Real.log (Real.log X)) := by
  intro N hXN
  induction N, hXN using Nat.le_induction with
  | base => simp
  | succ N hXN ih =>
    rw [Finset.sum_Ioc_succ_top hXN]
    have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
    have hXNr : (X : ℝ) ≤ N := by exact_mod_cast hXN
    push_cast
    have h1 := psiR_le (s := (N : ℝ) + 1) (by linarith)
    have h2 := inv_mul_log_le (n := (N : ℝ) + 1) (by linarith)
    rw [show (N : ℝ) + 1 - 1 = N by ring] at h2
    have h3 : KK / (((N : ℝ) + 1) * Real.log ((N : ℝ) + 1)) =
        KK * (1 / (((N : ℝ) + 1) * Real.log ((N : ℝ) + 1))) := by ring
    have hK := KK_pos
    nlinarith [mul_le_mul_of_nonneg_left h2 hK.le]

/-- `X ψ X ≤ KK / log X`. -/
theorem mul_psiR_le {X : ℝ} (hX : 10 ^ 8 ≤ X) : X * psiR X ≤ KK / Real.log X := by
  have hl : 0 < Real.log X := Real.log_pos (by linarith)
  unfold psiR
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hl]
  exact mul_gR_le hX

/-- **Inner bound.** For `10^8 ≤ X ≤ N`:
`Σ_{X<q≤N, q prime} g q ≤ 2 cA KK (log log N − log log X) + EE KK / log X`. -/
theorem inner_bound {X : ℕ} (hX : 10 ^ 8 ≤ X) {N : ℕ} (hXN : X ≤ N) :
    (∑ q ∈ Ioc X N, if q.Prime then gR q else 0) ≤
      2 * cA * KK * (Real.log (Real.log N) - Real.log (Real.log X)) + EE * KK / Real.log X := by
  have h1 := sum_g_le hX hXN
  have h2 := sum_psi_le hX N hXN
  have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
  have h3 := mul_psiR_le hX8
  have hc := cA_pos
  have hE := EE_pos
  have h4 : psiR X * (EE * X) ≤ EE * KK / Real.log X := by
    have : psiR X * (EE * X) = EE * (X * psiR X) := by ring
    rw [this, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h3 hE.le
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * cA)]

end MinModulus.Tail2
