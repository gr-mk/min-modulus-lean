import MinModulus.Tail2.Inner
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Tail2.Outer: the telescoping identity and the Abel potential with chords

STATUS: complete, no `sorry` (L2-T). Imports `Tail2.Inner` and Mathlib.

For a finite set `S` of numbers `> X` let `P_S(n) = ∏_{q ∈ S, q ≤ n} (1 + g q)` (`Pn`) and
`w s = 1/(2(3s−1))` (`wR`), so that `g p · w p = 1/(p−1)^2`.

* `term_eq`: `∏_{q ∈ S, q < p} (1 + g q) / (p−1)^2 = (P_S(p) − P_S(p−1)) · w p` for `p ∈ S`.
* `sum_term_eq`: `Σ_{p ∈ S, p ≤ N} … = Σ_{X < n ≤ N} (P_S(n) − P_S(n−1)) · w n` (all integers, no sorting).
* `abel_cell`: summation by parts on `(a, b]` with a potential `Φ` whose decrements dominate
  `(P n − 1)(w n − w (n+1))`.
* `outer_chain`: if `P_S(n) ≤ C₀ (1 + log(n/X)/L)^a` (`a ≥ 1`) for all `n ≥ X` and `U k` bounds the
  right side at the dyadic points `X·2^k` (`U` nondecreasing), then
  `Σ_{X<n≤X·2^J} (P_S(n) − P_S(n−1)) w n ≤ (P_S(X 2^J) − 1) w(X 2^J) +
     dW/6 · ((U 0 − 1)/X − (U J − 1)/(X 2^J) + Σ_{k<J} (U(k+1) − U k)/(log 2 · X 2^(k+1)))`.
  On each dyadic cell the convex function `v ↦ C₀ (1 + v/L)^a` lies below its chord
  `α + β log(s/T₀)`, and `Φ(s) = dW/6 · (α + β + β log(s/T₀))/s` has
  `(α + β log(s/T₀)) (1/s − 1/s') ≤ Φ(s) − Φ(s')` (`F_step`, from `log x ≤ x − 1`).
-/

namespace MinModulus.Tail2

open Finset Real

/-- `w s = 1/(2(3s−1))`, so that `g s · w s = 1/(s−1)^2`. -/
noncomputable def wR (s : ℝ) : ℝ := 1 / (2 * (3 * s - 1))

/-- The running product `P_S(n) = ∏_{q ∈ S, q ≤ n} (1 + g q)`. -/
noncomputable def Pn (S : Finset ℕ) (n : ℕ) : ℝ := ∏ q ∈ S.filter (· ≤ n), (1 + gR q)

/-- The slack factor `1 + 10^-8` of `w`. -/
noncomputable def dW : ℝ := 1 + 1 / 10 ^ 8

theorem dW_pos : 0 < dW := by unfold dW; positivity

/-! ### `w` -/

theorem gR_mul_wR {s : ℝ} (hs : 1 < s) : gR s * wR s = 1 / (s - 1) ^ 2 := by
  unfold gR wR
  have h1 : s - 1 ≠ 0 := by linarith
  have h2 : 3 * s - 1 ≠ 0 := by linarith
  field_simp

theorem wR_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ wR s := by
  unfold wR; apply div_nonneg zero_le_one; linarith

theorem wR_sub_nonneg {s : ℝ} (hs : 1 ≤ s) : 0 ≤ wR s - wR (s + 1) := by
  unfold wR
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (by linarith)
  linarith

theorem wR_sub_le {s : ℝ} (hs : 10 ^ 8 ≤ s) :
    wR s - wR (s + 1) ≤ dW / 6 * (1 / s - 1 / (s + 1)) := by
  unfold wR dW
  have hs0 : 0 < s := by linarith
  have e1 : 1 / (2 * (3 * s - 1)) - 1 / (2 * (3 * (s + 1) - 1)) =
      3 / (2 * ((3 * s - 1) * (3 * s + 2))) := by
    have h1 : 3 * s - 1 ≠ 0 := by linarith
    have h2 : 3 * s + 2 ≠ 0 := by linarith
    rw [show 3 * (s + 1) - 1 = 3 * s + 2 by ring]
    field_simp
    ring
  have e2 : 1 / s - 1 / (s + 1) = 1 / (s * (s + 1)) := by
    field_simp
    ring
  rw [e1, e2, mul_one_div, div_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

theorem wR_le {s : ℝ} (hs : 10 ^ 8 ≤ s) : wR s ≤ dW / 6 * (1 / s) := by
  unfold wR dW
  have hs0 : 0 < s := by linarith
  rw [mul_one_div, div_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-! ### The running product -/

theorem Pn_eq_one {S : Finset ℕ} {X n : ℕ} (hS : ∀ p ∈ S, X < p) (hn : n ≤ X) : Pn S n = 1 := by
  unfold Pn
  rw [Finset.filter_false_of_mem]
  · simp
  · intro q hq
    have := hS q hq
    omega

theorem one_le_Pn {S : Finset ℕ} (hS : ∀ p ∈ S, 1 ≤ p) (n : ℕ) : 1 ≤ Pn S n := by
  unfold Pn
  apply Finset.one_le_prod₀
  intro q hq
  have := gR_nonneg (s := (q : ℝ)) (by exact_mod_cast hS q (mem_filter.1 hq).1)
  linarith

theorem Pn_succ_of_not_mem {S : Finset ℕ} {n : ℕ} (hn : n + 1 ∉ S) : Pn S (n + 1) = Pn S n := by
  unfold Pn
  congr 1
  ext q
  simp only [mem_filter]
  constructor
  · rintro ⟨hq, hle⟩
    refine ⟨hq, ?_⟩
    rcases Nat.lt_or_ge q (n + 1) with h | h
    · omega
    · exact absurd (show q = n + 1 by omega ▸ hq) hn
  · rintro ⟨hq, hle⟩
    exact ⟨hq, by omega⟩

theorem Pn_succ_of_mem {S : Finset ℕ} {n : ℕ} (hn : n + 1 ∈ S) :
    Pn S (n + 1) = (1 + gR ((n + 1 : ℕ) : ℝ)) * Pn S n := by
  unfold Pn
  have hset : S.filter (· ≤ n + 1) = insert (n + 1) (S.filter (· ≤ n)) := by
    ext q
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hq, hle⟩
      rcases Nat.lt_or_ge q (n + 1) with h | h
      · exact Or.inr ⟨hq, by omega⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hq, hle⟩)
      · exact ⟨hn, le_rfl⟩
      · exact ⟨hq, by omega⟩
  rw [hset, Finset.prod_insert]
  simp

/-- **Telescoping identity.** For `p ∈ S`, `p ≥ 2`:
`∏_{q ∈ S, q < p} (1 + g q) / (p − 1)^2 = (P_S(p) − P_S(p − 1)) · w p`. -/
theorem term_eq {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) (hp2 : 2 ≤ p) :
    (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 = (Pn S p - Pn S (p - 1)) * wR p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hfil : S.filter (· < m + 1) = S.filter (· ≤ m) := by
    ext q; simp only [mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  rw [hfil, Pn_succ_of_mem hp, show m + 1 - 1 = m by omega]
  have hm : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < m + 1 by omega)
  have hgw := gR_mul_wR hm
  change (Pn S m) / (((m + 1 : ℕ) : ℝ) - 1) ^ 2 = _
  calc Pn S m / (((m + 1 : ℕ) : ℝ) - 1) ^ 2 = Pn S m * (gR ((m + 1 : ℕ) : ℝ) * wR ((m + 1 : ℕ) : ℝ)) := by
        rw [hgw, mul_one_div]
    _ = ((1 + gR ((m + 1 : ℕ) : ℝ)) * Pn S m - Pn S m) * wR ((m + 1 : ℕ) : ℝ) := by ring

/-- The tail sum over `S ∩ (X, N]` as a sum over all integers of `(X, N]`. -/
theorem sum_term_eq {S : Finset ℕ} {X : ℕ} (hS : ∀ p ∈ S, X < p) (hX : 1 ≤ X) (N : ℕ) :
    ∑ p ∈ S.filter (· ≤ N), (∏ q ∈ S.filter (· < p), (1 + gR q)) / ((p : ℝ) - 1) ^ 2 =
      ∑ n ∈ Ioc X N, (Pn S n - Pn S (n - 1)) * wR n := by
  have hsub : S.filter (· ≤ N) ⊆ Ioc X N := by
    intro p hp
    rw [mem_filter] at hp
    exact mem_Ioc.2 ⟨hS p hp.1, hp.2⟩
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [mem_filter] at hp
    exact term_eq hp.1 (by have := hS p hp.1; omega)
  · intro n hn hnS
    rw [mem_Ioc] at hn
    have hnS' : n ∉ S := fun h => hnS (mem_filter.2 ⟨h, hn.2⟩)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Pn_succ_of_not_mem hnS', show m + 1 - 1 = m by omega]
    ring

/-! ### Summation by parts on a cell -/

/-- **Abel summation on `(a, b]`** with a potential `Φ`. -/
theorem abel_cell (P w Φ : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ n, a ≤ n → n < b → (P n - 1) * (w n - w (n + 1)) ≤ Φ n - Φ (n + 1)) :
    ∑ n ∈ Ioc a b, (P n - P (n - 1)) * w n ≤
      (P b - 1) * w b - (P a - 1) * w a + Φ a - Φ b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, show b + 1 - 1 = b by omega]
    have h1 := ih fun n h1 h2 => hstep n h1 (by omega)
    have h2 := hstep b hab (by omega)
    linarith

/-! ### Chords of a convex power and the potential -/

/-- The chord bound for `v ↦ C (1 + v/L)^a` (`a ≥ 1`) on `[v₀, v₁]`. -/
theorem chord_le {a L C v₀ v₁ v U₀ U₁ : ℝ} (ha : 1 ≤ a) (hL : 0 < L) (hC : 0 ≤ C)
    (hv₀ : 0 ≤ v₀) (h01 : v₀ < v₁) (hv : v₀ ≤ v) (hv1 : v ≤ v₁)
    (hU₀ : C * (1 + v₀ / L) ^ a ≤ U₀) (hU₁ : C * (1 + v₁ / L) ^ a ≤ U₁) :
    C * (1 + v / L) ^ a ≤ U₀ + (U₁ - U₀) * ((v - v₀) / (v₁ - v₀)) := by
  set t := (v - v₀) / (v₁ - v₀) with ht
  have hd : 0 < v₁ - v₀ := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hd.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hd]; linarith
  have hx : 0 ≤ 1 + v₀ / L := by have := div_nonneg hv₀ hL.le; linarith
  have hy : 0 ≤ 1 + v₁ / L := by have := div_nonneg (hv₀.trans h01.le) hL.le; linarith
  have hconv := (convexOn_rpow ha).2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy)
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
  have hlin : (1 - t) • (1 + v₀ / L) + t • (1 + v₁ / L) = 1 + v / L := by
    simp only [smul_eq_mul]
    rw [ht]
    field_simp
    ring
  rw [hlin] at hconv
  simp only [smul_eq_mul] at hconv
  calc C * (1 + v / L) ^ a ≤ C * ((1 - t) * (1 + v₀ / L) ^ a + t * (1 + v₁ / L) ^ a) :=
        mul_le_mul_of_nonneg_left hconv hC
    _ = (1 - t) * (C * (1 + v₀ / L) ^ a) + t * (C * (1 + v₁ / L) ^ a) := by ring
    _ ≤ (1 - t) * U₀ + t * U₁ := by
        have h1t : 0 ≤ 1 - t := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hU₀ h1t, mul_le_mul_of_nonneg_left hU₁ ht0]
    _ = U₀ + (U₁ - U₀) * t := by ring

/-- `(α + β log(s/T)) (1/s − 1/s') ≤ F(s) − F(s')` for `F σ = (α + β + β log(σ/T))/σ`, `β ≥ 0`. -/
theorem F_step {α β T s s' : ℝ} (hβ : 0 ≤ β) (hT : 0 < T) (hs : 0 < s) (hss : s ≤ s') :
    (α + β * Real.log (s / T)) * (1 / s - 1 / s') ≤
      (α + β + β * Real.log (s / T)) / s - (α + β + β * Real.log (s' / T)) / s' := by
  have hs' : 0 < s' := hs.trans_le hss
  have hlog : Real.log (s' / T) = Real.log (s / T) + Real.log (s' / s) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hle : Real.log (s' / s) ≤ s' / s - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [hlog]
  have key : (α + β + β * Real.log (s / T)) / s -
      (α + β + β * (Real.log (s / T) + Real.log (s' / s))) / s' -
      (α + β * Real.log (s / T)) * (1 / s - 1 / s') =
      β * ((s' / s - 1) - Real.log (s' / s)) / s' := by
    field_simp
    ring
  have : 0 ≤ β * ((s' / s - 1) - Real.log (s' / s)) / s' :=
    div_nonneg (mul_nonneg hβ (by linarith)) hs'.le
  linarith

/-- The potential on the dyadic cell `[X 2^J, X 2^(J+1)]` with grid values `U₀ ≤ U₁`:
`Φ s = dW/6 · (U₀ − 1 + β + β log(s/(X 2^J)))/s`, `β = (U₁ − U₀)/log 2`. -/
noncomputable def Φc (X J : ℕ) (U₀ U₁ : ℝ) (s : ℝ) : ℝ :=
  dW / 6 * (((U₀ - 1) + (U₁ - U₀) / Real.log 2 +
    (U₁ - U₀) / Real.log 2 * Real.log (s / ((X : ℝ) * 2 ^ J))) / s)

/-- **One step inside a dyadic cell.** -/
theorem cell_step {S : Finset ℕ} {X : ℕ} (hX : 10 ^ 8 ≤ X) (hS1 : ∀ p ∈ S, 1 ≤ p)
    {C₀ a L : ℝ} (hC₀ : 0 ≤ C₀) (ha : 1 ≤ a) (hL : 0 < L)
    (hPn : ∀ n : ℕ, X ≤ n → Pn S n ≤ C₀ * (1 + Real.log (n / X) / L) ^ a)
    {J : ℕ} {U₀ U₁ : ℝ} (hU₀ : C₀ * (1 + J * Real.log 2 / L) ^ a ≤ U₀)
    (hU₁ : C₀ * (1 + (J + 1) * Real.log 2 / L) ^ a ≤ U₁) (hU : U₀ ≤ U₁)
    {n : ℕ} (hn0 : X * 2 ^ J ≤ n) (hn1 : n < X * 2 ^ (J + 1)) :
    (Pn S n - 1) * (wR n - wR ((n + 1 : ℕ) : ℝ)) ≤
      Φc X J U₀ U₁ n - Φc X J U₀ U₁ ((n + 1 : ℕ) : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hT0 : (0 : ℝ) < (X : ℝ) * 2 ^ J := by positivity
  have hn0r : (X : ℝ) * 2 ^ J ≤ n := by exact_mod_cast hn0
  have hn1r : (n : ℝ) ≤ (X : ℝ) * 2 ^ (J + 1) := by exact_mod_cast hn1.le
  have hXn : X ≤ n := le_trans (Nat.le_mul_of_pos_right X (by positivity)) hn0
  have hXnr : (X : ℝ) ≤ n := by exact_mod_cast hXn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn8 : (10 : ℝ) ^ 8 ≤ n := by linarith
  -- position in the cell
  set v := Real.log (n / X) with hv
  have hv0 : (J : ℝ) * Real.log 2 ≤ v := by
    rw [hv, ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    rw [le_div_iff₀ hXpos]; linarith
  have hv1 : v ≤ ((J : ℝ) + 1) * Real.log 2 := by
    rw [hv, show ((J : ℝ) + 1) = ((J + 1 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hXpos]; linarith
  have hvv : v - (J : ℝ) * Real.log 2 = Real.log (n / ((X : ℝ) * 2 ^ J)) := by
    rw [hv, ← Real.log_pow, ← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hchord := chord_le ha hL hC₀ (v₀ := (J : ℝ) * Real.log 2) (v₁ := ((J : ℝ) + 1) * Real.log 2)
    (v := v) (by positivity) (by nlinarith) hv0 hv1 hU₀ (by simpa using hU₁)
  rw [show ((J : ℝ) + 1) * Real.log 2 - (J : ℝ) * Real.log 2 = Real.log 2 by ring, hvv] at hchord
  set β := (U₁ - U₀) / Real.log 2 with hβ
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) hl2.le
  have hP := (hPn n hXn).trans hchord
  have hP' : Pn S n ≤ U₀ + β * Real.log (n / ((X : ℝ) * 2 ^ J)) := by
    have e : (U₁ - U₀) * (Real.log (n / ((X : ℝ) * 2 ^ J)) / Real.log 2) =
        β * Real.log (n / ((X : ℝ) * 2 ^ J)) := by rw [hβ]; ring
    linarith
  have hP1 : 0 ≤ Pn S n - 1 := by have := one_le_Pn hS1 n; linarith
  set A := U₀ - 1 + β * Real.log (n / ((X : ℝ) * 2 ^ J)) with hA
  have hPA : Pn S n - 1 ≤ A := by rw [hA]; linarith
  have hw0 : 0 ≤ wR n - wR ((n + 1 : ℕ) : ℝ) := by
    push_cast; exact wR_sub_nonneg (by linarith)
  have hw1 : wR n - wR ((n + 1 : ℕ) : ℝ) ≤ dW / 6 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
    push_cast; exact wR_sub_le hn8
  have hF := F_step (α := U₀ - 1) hβ0 hT0 hnpos (s' := (n : ℝ) + 1) (by linarith)
  have hA0 : 0 ≤ A := hP1.trans hPA
  have hd : 0 < dW / 6 := by have := dW_pos; positivity
  calc (Pn S n - 1) * (wR n - wR ((n + 1 : ℕ) : ℝ)) ≤ A * (wR n - wR ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hPA hw0
    _ ≤ A * (dW / 6 * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := mul_le_mul_of_nonneg_left hw1 hA0
    _ = dW / 6 * (A * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))) := by ring
    _ ≤ dW / 6 * ((U₀ - 1 + β + β * Real.log (n / ((X : ℝ) * 2 ^ J))) / n -
          (U₀ - 1 + β + β * Real.log (((n : ℝ) + 1) / ((X : ℝ) * 2 ^ J))) / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hF hd.le
    _ = Φc X J U₀ U₁ n - Φc X J U₀ U₁ ((n + 1 : ℕ) : ℝ) := by
        unfold Φc
        push_cast
        rw [← hβ]
        ring

/-- **The chain over the dyadic cells.** -/
theorem outer_chain {S : Finset ℕ} {X : ℕ} (hX : 10 ^ 8 ≤ X) (hS : ∀ p ∈ S, X < p)
    {C₀ a L : ℝ} (hC₀ : 0 ≤ C₀) (ha : 1 ≤ a) (hL : 0 < L)
    (hPn : ∀ n : ℕ, X ≤ n → Pn S n ≤ C₀ * (1 + Real.log (n / X) / L) ^ a)
    (U : ℕ → ℝ) (K : ℕ) (hU : ∀ k ≤ K, C₀ * (1 + k * Real.log 2 / L) ^ a ≤ U k)
    (hUm : ∀ k < K, U k ≤ U (k + 1)) :
    ∀ J ≤ K, ∑ n ∈ Ioc X (X * 2 ^ J), (Pn S n - Pn S (n - 1)) * wR n ≤
      (Pn S (X * 2 ^ J) - 1) * wR ((X * 2 ^ J : ℕ) : ℝ) +
        dW / 6 * ((U 0 - 1) / X - (U J - 1) / ((X : ℝ) * 2 ^ J) +
          ∑ k ∈ range J, (U (k + 1) - U k) / (Real.log 2 * ((X : ℝ) * 2 ^ (k + 1)))) := by
  have hS1 : ∀ p ∈ S, 1 ≤ p := fun p hp => by have := hS p hp; omega
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX8 : (10 : ℝ) ^ 8 ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := by linarith
  intro J
  induction J with
  | zero =>
    intro _
    simp [Pn_eq_one hS le_rfl]
  | succ J ih =>
    intro hJ
    have h1 := ih (by omega)
    have hT01 : X * 2 ^ J ≤ X * 2 ^ (J + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hXT : X ≤ X * 2 ^ J := Nat.le_mul_of_pos_right X (by positivity)
    rw [← Finset.sum_Ioc_consecutive _ hXT hT01]
    have hUJ := hU J (by omega)
    have hUJ1 := hU (J + 1) (by omega)
    push_cast at hUJ1
    have h2 := abel_cell (Pn S) (fun n => wR n) (fun n => Φc X J (U J) (U (J + 1)) n) hT01
      (fun n hn0 hn1 => cell_step hX hS1 hC₀ ha hL hPn hUJ hUJ1 (hUm J (by omega)) hn0 hn1)
    -- the potential at the two ends of the cell
    have hT0 : (0 : ℝ) < (X : ℝ) * 2 ^ J := by positivity
    have hΦ0 : Φc X J (U J) (U (J + 1)) ((X * 2 ^ J : ℕ) : ℝ) =
        dW / 6 * ((U J - 1 + (U (J + 1) - U J) / Real.log 2) / ((X : ℝ) * 2 ^ J)) := by
      unfold Φc; push_cast
      rw [div_self hT0.ne', Real.log_one]; ring
    have hΦ1 : Φc X J (U J) (U (J + 1)) ((X * 2 ^ (J + 1) : ℕ) : ℝ) =
        dW / 6 * ((U (J + 1) - 1 + (U (J + 1) - U J) / Real.log 2) / ((X : ℝ) * 2 ^ (J + 1))) := by
      unfold Φc; push_cast
      rw [show (X : ℝ) * 2 ^ (J + 1) / ((X : ℝ) * 2 ^ J) = 2 by rw [pow_succ]; field_simp]
      field_simp
      ring
    rw [hΦ0, hΦ1] at h2
    rw [Finset.sum_range_succ]
    have e : (X : ℝ) * 2 ^ (J + 1) = 2 * ((X : ℝ) * 2 ^ J) := by rw [pow_succ]; ring
    rw [e] at h2 ⊢
    have key : dW / 6 * ((U J - 1 + (U (J + 1) - U J) / Real.log 2) / ((X : ℝ) * 2 ^ J)) -
        dW / 6 * ((U (J + 1) - 1 + (U (J + 1) - U J) / Real.log 2) / (2 * ((X : ℝ) * 2 ^ J))) =
        dW / 6 * ((U J - 1) / ((X : ℝ) * 2 ^ J) - (U (J + 1) - 1) / (2 * ((X : ℝ) * 2 ^ J)) +
          (U (J + 1) - U J) / (Real.log 2 * (2 * ((X : ℝ) * 2 ^ J)))) := by
      field_simp
      ring
    push_cast at h1 h2 ⊢
    linarith [h1, h2, key]

end MinModulus.Tail2
