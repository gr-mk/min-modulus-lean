import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Module 1 (`Comparison`): the hinge comparison theorem on finite products

## Status

**Complete, no `sorry`.**  `#print axioms` for `comparison`, `aligned_eq_vLaw` and
`comparison_vLaw` gives `[propext, Classical.choice, Quot.sound]`.

## Setting

* `n` coordinates, `X : Fin n → Type u`, each a `Fintype` with `DecidableEq`; points are
  `x : (j : Fin n) → X j`; `N_j = Fintype.card (X j)`.
* The measure is `μ x = ∏ j, K j x (x j)`, where the kernel `K j x y` depends only on the
  coordinates `x i` with `i < j` (hypothesis `hKdep`), `K ≥ 0`, `∑_y K j x y = 1`,
  `K j x y ≤ ν_j / N_j`, and `1 ≤ ν_j`.
* A finite family `I` of "rectangles" `S c : (j : Fin n) → Finset (X j)` with weights `w c ≥ 0`.
  The rectangles are arbitrary finsets; only their cardinalities enter the aligned side.

## Main results

* `greedyW ν N k = min ν (max 0 (N - ν k))`; `sum_range_greedyW` (partial sums
  `∑_{k<M} greedyW = min (ν M) N`, valid for every `M`), `sum_range_greedyW_self` (`= N` for
  `ν ≥ 1`).
* `hinge_majorization`, `one_coord` (density form), `one_coord_kernel` (kernel form): the
  one-coordinate lemma, proved by LP duality (no sorting).
* `comparison`: the main theorem
  ```
  ∑_x μ x · max 0 (∑_c w_c·[∀ j, x j ∈ S c j] − t)
    ≤ ∑_{k : ∀ j, Fin N_j} (∏_j greedyW ν_j N_j k_j / N_j) · max 0 (∑_c w_c·[∀ j, k_j < |S c j|] − t)
  ```
* `aligned_eq_vLaw`: if `N_j = q_j^{e_j}` and `|S c j| = q_j^{e_j − a c j}`, the aligned side is
  `E_V[max 0 (∑_c w_c [∀ j, a c j ≤ V_j] − t)]`, with independent `V_j ∈ {0..e_j}` of law
  `vLaw (q j) (ν j) (e j)`, i.e. `P(V_j ≥ r) = vTail q ν r = min 1 (ν q^{-r})` for `r ≤ e_j`.
* `comparison_vLaw`: the combination of the two.
* Facts about the V-law: `vTail_eq_ite` (for `1 ≤ ν ≤ q` it is `if r = 0 then 1 else ν (q⁻¹)^r`,
  literally the body of `Smooth.tailP`), `vLaw_cap_zero`, `vLaw_zero`, `vLaw_mid`, `vLaw_top`
  (explicit values), `vLaw_nonneg` and `prod_vLaw_nonneg` (need only `1 ≤ q`, `0 ≤ ν`),
  `sum_vLaw` (total mass 1).

## Proof structure

* One coordinate. `F y = ∑_l w_l [y ∈ B_l]`, `G k = ∑_l w_l [k < |B_l|]` (nonincreasing).
  (a) `hinge_majorization`: `∑_y (F y − s)^+ ≤ ∑_{k<N} (G k − s)^+` for every `s`, via the
  superlevel set `T = {F > s}` and `|T ∩ B_l| ≤ min(|T|, |B_l|)`.
  (b) LP step: `∑ κ (F − t)^+ ≤ λ N + ν ∑ (F − t − λ)^+` for `λ ≥ 0`.
  (c) With `K0 = ⌊N/ν⌋₊`, `λ = (G K0 − t)^+`, the bound equals `∑_k greedyW_k (G k − t)^+`
  termwise (`greedyW = ν` below `K0`, `= 0` above `K0`).
* Main theorem: induction on `n`, peeling the **first** coordinate (`Fin.cons`,
  `Fin.consEquiv`, `Fin.prod_univ_succ`).  For each value `a` of the first coordinate, the
  induction hypothesis is applied to the kernels `K (succ j) (cons a ·)` and the weights
  `w_c [a ∈ S c 0]`; then, after swapping sums, the one-coordinate lemma is applied to the first
  coordinate (kernel `K 0`, which is constant) once for each tail index `k'`, with weights
  `w_c [∀ j, k'_j < |S c (succ j)|]`.
* V-law: the map `vIdx q e : Fin (q^e) → Fin (e+1)`, `k ↦ e − ⌈log_q (k+1)⌉`, satisfies
  `r ≤ vIdx k ↔ k < q^(e−r)` (`le_vIdx_iff`), so the aligned indicator factors through it; the
  pushforward of the greedy product weight (`sum_pi_pushforward`) has tails
  `min(ν q^{e−r}, q^e)/q^e = min 1 (ν q^{-r})` by the partial-sum formula.

## Deviations from `LEAN_DESIGN.md` (all harmless or strengthenings)

* `w_c · [P]` is written `if P then w c else 0`.
* No hypothesis `0 ≤ t` is needed (`t : ℝ` is arbitrary), and no `Nonempty (X j)` is needed.
* The induction peels the first coordinate instead of the last (same mathematics).
* The one-coordinate lemma has no separate constant `c`: it is the case `B_l = univ`.
* `sum_range_greedyW` holds for every `M` (not only `M ≤ N`) and needs only `0 ≤ ν`.
* `aligned_eq_vLaw` needs `1 < q_j` and `0 ≤ ν_j` (it is an identity; `ν ≥ 1` is not needed).
* The V-law is indexed by `v : (j : Fin n) → Fin (e j + 1)`, weight `∏ j, vLaw (q j) (ν j) (e j) (v j)`.
-/

namespace MinModulus.Comparison

open Finset

universe u v

/-! ## Greedy weights -/

/-- The greedy weights `greedyW ν N k = min ν (max 0 (N − ν k))`, for `k = 0, …, N − 1`. They put
mass `ν` on the first `⌊N/ν⌋` indices and the remainder on the next one. -/
noncomputable def greedyW (ν : ℝ) (N k : ℕ) : ℝ := min ν (max 0 ((N : ℝ) - ν * k))

theorem greedyW_nonneg {ν : ℝ} (hν : 0 ≤ ν) (N k : ℕ) : 0 ≤ greedyW ν N k :=
  le_min hν (le_max_left _ _)

theorem greedyW_le (ν : ℝ) (N k : ℕ) : greedyW ν N k ≤ ν := min_le_left _ _

/-- Partial sums of the greedy weights: `∑_{k<M} greedyW ν N k = min (ν M) N` (any `M`). -/
theorem sum_range_greedyW {ν : ℝ} (hν : 0 ≤ ν) (N M : ℕ) :
    ∑ k ∈ range M, greedyW ν N k = min (ν * M) N := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, greedyW]
    push_cast
    rcases le_or_gt (ν * M) N with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]
      rcases le_or_gt ν (N - ν * M) with h2 | h2
      · rw [min_eq_left h2, min_eq_left (by linarith)]; ring
      · rw [min_eq_right h2.le, min_eq_right (by linarith)]; ring
    · rw [min_eq_right h.le, max_eq_left (by linarith), min_eq_right hν,
        min_eq_right (by linarith)]
      ring

/-- The greedy weights sum to `N` (for `ν ≥ 1`). -/
theorem sum_range_greedyW_self {ν : ℝ} (hν : 1 ≤ ν) (N : ℕ) :
    ∑ k ∈ range N, greedyW ν N k = N := by
  rw [sum_range_greedyW (by linarith), min_eq_right]
  exact le_mul_of_one_le_left (Nat.cast_nonneg N) hν

/-- The greedy weights sum to `N` (for `ν ≥ 1`), `Fin`-indexed form. -/
theorem sum_fin_greedyW {ν : ℝ} (hν : 1 ≤ ν) (N : ℕ) :
    ∑ k : Fin N, greedyW ν N k = N := by
  rw [Fin.sum_univ_eq_sum_range (fun k => greedyW ν N k) N, sum_range_greedyW_self hν]

theorem greedyW_of_lt_floor {ν : ℝ} (hν : 0 < ν) {N k : ℕ} (hk : k < ⌊(N : ℝ) / ν⌋₊) :
    greedyW ν N k = ν := by
  have h1 : ((k : ℝ) + 1) ≤ (N : ℝ) / ν := by
    have : ((k + 1 : ℕ) : ℝ) ≤ (⌊(N : ℝ) / ν⌋₊ : ℝ) := Nat.cast_le.mpr hk
    push_cast at this
    exact this.trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hν.le))
  rw [le_div_iff₀ hν] at h1
  rw [greedyW, max_eq_right (by nlinarith), min_eq_left (by nlinarith)]

theorem greedyW_of_floor_lt {ν : ℝ} (hν : 0 < ν) {N k : ℕ} (hk : ⌊(N : ℝ) / ν⌋₊ < k) :
    greedyW ν N k = 0 := by
  have h1 : (N : ℝ) / ν < k := by
    have := Nat.lt_floor_add_one ((N : ℝ) / ν)
    have h2 : ((⌊(N : ℝ) / ν⌋₊ + 1 : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    push_cast at h2
    linarith
  rw [div_lt_iff₀ hν] at h1
  rw [greedyW, max_eq_left (by nlinarith), min_eq_right hν.le]

/-! ## The one-coordinate lemma -/

/-- `∑_{k<K} [k < b]·x = x · min K b`. -/
theorem sum_range_ite_lt (K b : ℕ) (x : ℝ) :
    ∑ k ∈ range K, (if k < b then x else 0) = x * (min K b : ℕ) := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have : (range K).filter (fun k => k < b) = range (min K b) := by
    ext k; simp [lt_min_iff]
  rw [this, card_range]

/-- (a) Hinge majorization: for every level `s`,
`∑_y (F y − s)^+ ≤ ∑_{k<N} (G k − s)^+`, where `F y = ∑_l w_l [y ∈ B_l]` and
`G k = ∑_l w_l [k < |B_l|]`. -/
theorem hinge_majorization {Y : Type*} [Fintype Y] [DecidableEq Y] {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ l, 0 ≤ w l) (B : I → Finset Y) (s : ℝ) :
    ∑ y, max 0 (∑ l, (if y ∈ B l then w l else 0) - s) ≤
      ∑ k ∈ range (Fintype.card Y), max 0 (∑ l, (if k < (B l).card then w l else 0) - s) := by
  set T : Finset Y := univ.filter (fun y => s < ∑ l, (if y ∈ B l then w l else 0)) with hT
  have hTN : T.card ≤ Fintype.card Y := card_le_univ T
  have h1 : ∑ y, max 0 (∑ l, (if y ∈ B l then w l else 0) - s)
      = ∑ y ∈ T, (∑ l, (if y ∈ B l then w l else 0) - s) := by
    rw [hT, sum_filter]
    refine sum_congr rfl fun y _ => ?_
    split_ifs with h
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  have h2 : ∑ y ∈ T, (∑ l, (if y ∈ B l then w l else 0) - s)
      = ∑ l, w l * ((T ∩ B l).card : ℝ) - T.card * s := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, sum_comm]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    rw [sum_ite_mem, sum_const, nsmul_eq_mul, mul_comm]
  have h3 : ∑ k ∈ range T.card, (∑ l, (if k < (B l).card then w l else 0) - s)
      = ∑ l, w l * ((min T.card (B l).card : ℕ) : ℝ) - T.card * s := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sum_comm]
    congr 1
    exact sum_congr rfl fun l _ => sum_range_ite_lt _ _ _
  have h4 : ∑ l, w l * ((T ∩ B l).card : ℝ) ≤
      ∑ l, w l * ((min T.card (B l).card : ℕ) : ℝ) := by
    refine sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hw l)
    exact_mod_cast le_min (card_le_card inter_subset_left) (card_le_card inter_subset_right)
  calc ∑ y, max 0 (∑ l, (if y ∈ B l then w l else 0) - s)
      = ∑ k ∈ range T.card, (∑ l, (if k < (B l).card then w l else 0) - s)
        - (∑ l, w l * ((min T.card (B l).card : ℕ) : ℝ) - ∑ l, w l * ((T ∩ B l).card : ℝ)) := by
        rw [h1, h2, h3]; ring
    _ ≤ ∑ k ∈ range T.card, (∑ l, (if k < (B l).card then w l else 0) - s) := by linarith
    _ ≤ ∑ k ∈ range T.card, max 0 (∑ l, (if k < (B l).card then w l else 0) - s) :=
        sum_le_sum fun k _ => le_max_right _ _
    _ ≤ ∑ k ∈ range (Fintype.card Y), max 0 (∑ l, (if k < (B l).card then w l else 0) - s) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hTN) fun _ _ _ => le_max_left _ _

/-- **One-coordinate lemma** (density form). Let `Y` have `N` elements and `κ` be a density
w.r.t. counting measure normalized to total mass `N` (`κ ≥ 0`, `∑ κ = N`, `κ ≤ ν`, `ν ≥ 1`).
Then for `F y = ∑_l w_l [y ∈ B_l]` (`w ≥ 0`), `G k = ∑_l w_l [k < |B_l|]` and any `t`,
`∑_y κ y (F y − t)^+ ≤ ∑_{k<N} greedyW ν N k · (G k − t)^+`. -/
theorem one_coord {Y : Type*} [Fintype Y] [DecidableEq Y] {I : Type*} [Fintype I]
    (κ : Y → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hκ0 : ∀ y, 0 ≤ κ y)
    (hκsum : ∑ y, κ y = Fintype.card Y) (hκν : ∀ y, κ y ≤ ν)
    (w : I → ℝ) (hw : ∀ l, 0 ≤ w l) (B : I → Finset Y) (t : ℝ) :
    ∑ y, κ y * max 0 (∑ l, (if y ∈ B l then w l else 0) - t) ≤
      ∑ k ∈ range (Fintype.card Y), greedyW ν (Fintype.card Y) k *
        max 0 (∑ l, (if k < (B l).card then w l else 0) - t) := by
  have hνpos : 0 < ν := by linarith
  -- the aligned profile `G` and its hinge
  set G : ℕ → ℝ := fun k => ∑ l, (if k < (B l).card then w l else 0) with hG
  have hG_anti : Antitone G := by
    intro k k' hkk'
    refine sum_le_sum fun l _ => ?_
    by_cases h' : k' < (B l).card
    · rw [ite_eq_left h', ite_eq_left (lt_of_le_of_lt hkk' h')]
    · rw [ite_eq_right h']
      split_ifs
      exacts [hw l, le_rfl]
  have hg_anti : ∀ k k', k ≤ k' → max 0 (G k' - t) ≤ max 0 (G k - t) := fun k k' h =>
    max_le_max le_rfl (by linarith [hG_anti h])
  -- the dual variable
  set K0 : ℕ := ⌊(Fintype.card Y : ℝ) / ν⌋₊ with hK0
  set lam : ℝ := max 0 (G K0 - t) with hlam
  have hlam0 : 0 ≤ lam := le_max_left _ _
  -- (b) LP-duality step
  have hLP : ∑ y, κ y * max 0 (∑ l, (if y ∈ B l then w l else 0) - t) ≤
      lam * Fintype.card Y + ν * ∑ y, max 0 (∑ l, (if y ∈ B l then w l else 0) - (t + lam)) := by
    have hpt : ∀ y, κ y * max 0 (∑ l, (if y ∈ B l then w l else 0) - t) ≤
        κ y * lam + ν * max 0 (∑ l, (if y ∈ B l then w l else 0) - (t + lam)) := by
      intro y
      set F := ∑ l, (if y ∈ B l then w l else 0)
      have h1 : max 0 (F - t) ≤ lam + max 0 (F - (t + lam)) := by
        apply max_le
        · linarith [le_max_left 0 (F - (t + lam))]
        · linarith [le_max_right 0 (F - (t + lam))]
      have h2 : 0 ≤ max 0 (F - (t + lam)) := le_max_left _ _
      calc κ y * max 0 (F - t) ≤ κ y * (lam + max 0 (F - (t + lam))) :=
            mul_le_mul_of_nonneg_left h1 (hκ0 y)
        _ = κ y * lam + κ y * max 0 (F - (t + lam)) := by ring
        _ ≤ κ y * lam + ν * max 0 (F - (t + lam)) := by
            gcongr
            exact hκν y
    calc _ ≤ ∑ y, (κ y * lam + ν * max 0 (∑ l, (if y ∈ B l then w l else 0) - (t + lam))) :=
          sum_le_sum fun y _ => hpt y
      _ = _ := by rw [sum_add_distrib, ← sum_mul, hκsum, ← mul_sum]; ring
  -- (a) hinge majorization at level `t + lam`
  have hmaj := hinge_majorization w hw B (t + lam)
  -- (c) termwise identity for the greedy weights
  have hpt : ∀ k, greedyW ν (Fintype.card Y) k * lam + ν * max 0 (G k - (t + lam)) ≤
      greedyW ν (Fintype.card Y) k * max 0 (G k - t) := by
    intro k
    have e1 : max 0 (G k - (t + lam)) = max 0 (max 0 (G k - t) - lam) := by
      rcases le_total 0 (G k - t) with h | h
      · rw [max_eq_right h, sub_sub]
      · rw [max_eq_left h, max_eq_left (by linarith), max_eq_left (by linarith)]
    rw [e1]
    rcases lt_trichotomy k K0 with h | h | h
    · rw [greedyW_of_lt_floor hνpos h, max_eq_right (by linarith [hg_anti k K0 h.le])]
      ring_nf
      exact le_rfl
    · subst h
      rw [← hlam, sub_self, max_self]
      simp
    · rw [greedyW_of_floor_lt hνpos h, max_eq_left (by linarith [hg_anti K0 k h.le])]
      simp
  calc _ ≤ lam * Fintype.card Y +
        ν * ∑ y, max 0 (∑ l, (if y ∈ B l then w l else 0) - (t + lam)) := hLP
    _ ≤ lam * Fintype.card Y + ν * ∑ k ∈ range (Fintype.card Y), max 0 (G k - (t + lam)) := by
        gcongr
    _ = ∑ k ∈ range (Fintype.card Y),
          (greedyW ν (Fintype.card Y) k * lam + ν * max 0 (G k - (t + lam))) := by
        rw [sum_add_distrib, ← sum_mul, sum_range_greedyW_self hν, ← mul_sum]
        ring
    _ ≤ _ := sum_le_sum fun k _ => hpt k

/-- **One-coordinate lemma** (kernel form): `κ` is a probability kernel on `Y` with
`κ ≤ ν / N`. -/
theorem one_coord_kernel {Y : Type*} [Fintype Y] [DecidableEq Y] {I : Type*} [Fintype I]
    (κ : Y → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hκ0 : ∀ y, 0 ≤ κ y) (hκ1 : ∑ y, κ y = 1)
    (hκν : ∀ y, κ y ≤ ν / Fintype.card Y)
    (w : I → ℝ) (hw : ∀ l, 0 ≤ w l) (B : I → Finset Y) (t : ℝ) :
    ∑ y, κ y * max 0 (∑ l, (if y ∈ B l then w l else 0) - t) ≤
      ∑ k : Fin (Fintype.card Y), greedyW ν (Fintype.card Y) k / Fintype.card Y *
        max 0 (∑ l, (if (k : ℕ) < (B l).card then w l else 0) - t) := by
  have hNpos : 0 < Fintype.card Y := by
    rw [Fintype.card_pos_iff]
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hκ1
  have hN : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr hNpos
  have key := one_coord (fun y => (Fintype.card Y : ℝ) * κ y) ν hν
    (fun y => mul_nonneg hN.le (hκ0 y)) (by rw [← mul_sum, hκ1, mul_one])
    (fun y => by have := hκν y; rw [le_div_iff₀ hN] at this; linarith) w hw B t
  rw [Fin.sum_univ_eq_sum_range (fun k => greedyW ν (Fintype.card Y) k / Fintype.card Y *
    max 0 (∑ l, (if k < (B l).card then w l else 0) - t)) (Fintype.card Y)]
  have e : ∑ k ∈ range (Fintype.card Y), greedyW ν (Fintype.card Y) k / Fintype.card Y *
      max 0 (∑ l, (if k < (B l).card then w l else 0) - t) =
      (∑ k ∈ range (Fintype.card Y), greedyW ν (Fintype.card Y) k *
      max 0 (∑ l, (if k < (B l).card then w l else 0) - t)) / Fintype.card Y := by
    rw [sum_div]
    exact sum_congr rfl fun k _ => by ring
  rw [e, le_div_iff₀ hN, sum_mul]
  refine le_trans (le_of_eq ?_) key
  exact sum_congr rfl fun y _ => by ring

/-! ## The main theorem -/

/-- A sum over `(j : Fin (n+1)) → α j` split into the first coordinate and the rest. -/
theorem sum_pi_fin_succ {n : ℕ} {α : Fin (n + 1) → Type*} [∀ j, Fintype (α j)]
    (f : ((j : Fin (n + 1)) → α j) → ℝ) :
    ∑ x, f x = ∑ a : α 0, ∑ x' : (j : Fin n) → α j.succ, f (Fin.cons a x') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv α) _ _ (fun _ => rfl)).symm

theorem ite_ite_zero_comm (P Q : Prop) [Decidable P] [Decidable Q] (w : ℝ) :
    (if P then (if Q then w else 0) else 0) = if Q then (if P then w else 0) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem ite_forall_fin_succ {n : ℕ} (P : Fin (n + 1) → Prop) [DecidablePred P] (w : ℝ) :
    (if ∀ j, P j then w else 0) = if P 0 then (if ∀ j : Fin n, P j.succ then w else 0) else 0 := by
  by_cases h0 : P 0 <;> by_cases h1 : ∀ j : Fin n, P j.succ <;> simp [Fin.forall_fin_succ, h0, h1]

theorem ite_forall_fin_succ' {n : ℕ} (P : Fin (n + 1) → Prop) [DecidablePred P] (w : ℝ) :
    (if ∀ j, P j then w else 0) = if ∀ j : Fin n, P j.succ then (if P 0 then w else 0) else 0 := by
  rw [ite_forall_fin_succ, ite_ite_zero_comm]

/-- The main theorem, with everything after `n` universally quantified (for the induction). -/
theorem comparison_aux (t : ℝ) {I : Type v} [Fintype I] (n : ℕ) :
    ∀ (X : Fin n → Type u) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
      (K : (j : Fin n) → ((i : Fin n) → X i) → X j → ℝ) (ν : Fin n → ℝ),
      (∀ j x y, 0 ≤ K j x y) → (∀ j x, ∑ y, K j x y = 1) →
      (∀ j x y, K j x y ≤ ν j / Fintype.card (X j)) → (∀ j, 1 ≤ ν j) →
      (∀ j x x', (∀ i, i < j → x i = x' i) → K j x = K j x') →
      ∀ (w : I → ℝ), (∀ c, 0 ≤ w c) → ∀ (S : I → (j : Fin n) → Finset (X j)),
      ∑ x : (j : Fin n) → X j, (∏ j, K j x (x j)) *
          max 0 (∑ c, (if ∀ j, x j ∈ S c j then w c else 0) - t)
        ≤ ∑ k : (j : Fin n) → Fin (Fintype.card (X j)),
            (∏ j, greedyW (ν j) (Fintype.card (X j)) (k j) / Fintype.card (X j)) *
              max 0 (∑ c, (if ∀ j, (k j : ℕ) < (S c j).card then w c else 0) - t) := by
  induction n with
  | zero =>
    intro X _ _ K ν _ _ _ _ _ w _ S
    apply le_of_eq
    simp
  | succ n ih =>
    intro X _ _ K ν hK0 hK1 hKν hν hKdep w hw S
    rcases isEmpty_or_nonempty ((j : Fin (n + 1)) → X j) with hE | hne
    · rw [univ_eq_empty, sum_empty]
      exact sum_nonneg fun k _ => mul_nonneg (prod_nonneg fun j _ => div_nonneg
        (greedyW_nonneg (by linarith [hν j]) _ _) (Nat.cast_nonneg _)) (le_max_left _ _)
    obtain ⟨p⟩ := hne
    -- the first kernel does not depend on the point
    have hK0p : ∀ x, K 0 x = K 0 p := fun x =>
      hKdep 0 x p (fun i hi => absurd hi (Fin.not_lt_zero i))
    -- induction hypothesis, for each value `a` of the first coordinate
    have hIH : ∀ a : X 0,
        ∑ x' : (j : Fin n) → X j.succ, (∏ j : Fin n, K j.succ (Fin.cons a x') (x' j)) *
            max 0 (∑ c, (if ∀ j : Fin n, x' j ∈ S c j.succ then
              (if a ∈ S c 0 then w c else 0) else 0) - t)
          ≤ ∑ k' : (j : Fin n) → Fin (Fintype.card (X j.succ)),
            (∏ j : Fin n, greedyW (ν j.succ) (Fintype.card (X j.succ)) (k' j) /
              Fintype.card (X j.succ)) *
              max 0 (∑ c, (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then
                (if a ∈ S c 0 then w c else 0) else 0) - t) := by
      intro a
      exact ih (fun j => X j.succ) (fun j x' z => K j.succ (Fin.cons a x') z) (fun j => ν j.succ)
        (fun j x' z => hK0 _ _ _) (fun j x' => hK1 _ _) (fun j x' z => hKν _ _ _)
        (fun j => hν _)
        (by
          intro j x' x'' h
          apply hKdep
          intro i hi
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
          · rfl
          · simp only [Fin.cons_succ]
            exact h i' (Fin.succ_lt_succ_iff.mp hi))
        (fun c => if a ∈ S c 0 then w c else 0)
        (fun c => by split_ifs; exacts [hw c, le_rfl])
        (fun c j => S c j.succ)
    -- one-coordinate lemma in the first coordinate, for each tail index `k'`
    have hOne : ∀ k' : (j : Fin n) → Fin (Fintype.card (X j.succ)),
        ∑ a : X 0, K 0 p a * max 0 (∑ c, (if a ∈ S c 0 then
            (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then w c else 0) else 0) - t)
          ≤ ∑ k₀ : Fin (Fintype.card (X 0)),
            greedyW (ν 0) (Fintype.card (X 0)) k₀ / Fintype.card (X 0) *
              max 0 (∑ c, (if (k₀ : ℕ) < (S c 0).card then
                (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then w c else 0) else 0) - t) := by
      intro k'
      exact one_coord_kernel (K 0 p) (ν 0) (hν 0) (hK0 0 p) (hK1 0 p) (hKν 0 p)
        (fun c => if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then w c else 0)
        (fun c => by split_ifs; exacts [hw c, le_rfl]) (fun c => S c 0) t
    calc _ = ∑ a : X 0, K 0 p a * ∑ x' : (j : Fin n) → X j.succ,
            (∏ j : Fin n, K j.succ (Fin.cons a x') (x' j)) *
            max 0 (∑ c, (if ∀ j : Fin n, x' j ∈ S c j.succ then
              (if a ∈ S c 0 then w c else 0) else 0) - t) := by
          rw [sum_pi_fin_succ]
          refine sum_congr rfl fun a _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun x' _ => ?_
          rw [Fin.prod_univ_succ, Fin.cons_zero, hK0p (Fin.cons a x'), mul_assoc]
          simp only [Fin.cons_succ, ite_forall_fin_succ', Fin.cons_zero]
      _ ≤ ∑ a : X 0, K 0 p a * ∑ k' : (j : Fin n) → Fin (Fintype.card (X j.succ)),
            (∏ j : Fin n, greedyW (ν j.succ) (Fintype.card (X j.succ)) (k' j) /
              Fintype.card (X j.succ)) *
              max 0 (∑ c, (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then
                (if a ∈ S c 0 then w c else 0) else 0) - t) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hIH a) (hK0 0 p a)
      _ = ∑ k' : (j : Fin n) → Fin (Fintype.card (X j.succ)),
            (∏ j : Fin n, greedyW (ν j.succ) (Fintype.card (X j.succ)) (k' j) /
              Fintype.card (X j.succ)) *
            ∑ a : X 0, K 0 p a * max 0 (∑ c, (if a ∈ S c 0 then
              (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then w c else 0) else 0) - t) := by
          simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun k' _ => sum_congr rfl fun a _ => ?_
          have e : ∀ c, (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then
                (if a ∈ S c 0 then w c else 0) else 0) = (if a ∈ S c 0 then
              (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then w c else 0) else 0) :=
            fun c => ite_ite_zero_comm _ _ _
          simp only [e]
          ring
      _ ≤ ∑ k' : (j : Fin n) → Fin (Fintype.card (X j.succ)),
            (∏ j : Fin n, greedyW (ν j.succ) (Fintype.card (X j.succ)) (k' j) /
              Fintype.card (X j.succ)) *
            ∑ k₀ : Fin (Fintype.card (X 0)),
              greedyW (ν 0) (Fintype.card (X 0)) k₀ / Fintype.card (X 0) *
              max 0 (∑ c, (if (k₀ : ℕ) < (S c 0).card then
                (if ∀ j : Fin n, (k' j : ℕ) < (S c j.succ).card then w c else 0) else 0) - t) :=
          sum_le_sum fun k' _ => mul_le_mul_of_nonneg_left (hOne k')
            (prod_nonneg fun j _ => div_nonneg (greedyW_nonneg (by linarith [hν j.succ]) _ _)
              (Nat.cast_nonneg _))
      _ = _ := by
          symm
          rw [sum_pi_fin_succ, sum_comm]
          refine sum_congr rfl fun k' _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun k₀ _ => ?_
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_succ, Fin.cons_zero, ite_forall_fin_succ]
          ring

/-- **Hinge comparison theorem on finite products.**

`μ x = ∏ j, K j x (x j)` with kernels `K j x ·` that depend only on `x i` for `i < j`, are
probability vectors, and are bounded by `ν j / N_j` (`ν j ≥ 1`).  For nonnegative weights `w` on
rectangles `S c = ∏_j S c j` and any `t`,
`E_μ[(∑_c w_c 1_{S c} − t)^+]` is at most the aligned sum, in which coordinate `j` is replaced by
`k_j ∈ Fin N_j` with weight `greedyW ν_j N_j k_j / N_j` and `x_j ∈ S c j` by `k_j < |S c j|`. -/
theorem comparison {n : ℕ} {X : Fin n → Type u} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (K : (j : Fin n) → ((i : Fin n) → X i) → X j → ℝ) (ν : Fin n → ℝ)
    (hK0 : ∀ j x y, 0 ≤ K j x y) (hK1 : ∀ j x, ∑ y, K j x y = 1)
    (hKν : ∀ j x y, K j x y ≤ ν j / Fintype.card (X j)) (hν : ∀ j, 1 ≤ ν j)
    (hKdep : ∀ j x x', (∀ i, i < j → x i = x' i) → K j x = K j x')
    {I : Type v} [Fintype I] (w : I → ℝ) (hw : ∀ c, 0 ≤ w c)
    (S : I → (j : Fin n) → Finset (X j)) (t : ℝ) :
    ∑ x : (j : Fin n) → X j, (∏ j, K j x (x j)) *
        max 0 (∑ c, (if ∀ j, x j ∈ S c j then w c else 0) - t)
      ≤ ∑ k : (j : Fin n) → Fin (Fintype.card (X j)),
          (∏ j, greedyW (ν j) (Fintype.card (X j)) (k j) / Fintype.card (X j)) *
            max 0 (∑ c, (if ∀ j, (k j : ℕ) < (S c j).card then w c else 0) - t) :=
  comparison_aux t n X K ν hK0 hK1 hKν hν hKdep w hw S

/-! ## The V-law -/

/-- `vTail q ν r = P(V ≥ r) = min 1 (ν q^{-r})`. -/
noncomputable def vTail (q : ℕ) (ν : ℝ) (r : ℕ) : ℝ := min 1 (ν / (q : ℝ) ^ r)

/-- The law of `min(V, e)`: `vLaw q ν e r = P(V = r)` for `r < e`, and `P(V ≥ e)` for `r = e`. -/
noncomputable def vLaw (q : ℕ) (ν : ℝ) (e r : ℕ) : ℝ :=
  if r < e then vTail q ν r - vTail q ν (r + 1) else vTail q ν e

/-- The level of an aligned index `k ∈ [0, q^e)`: `vIdx q e k = e − ⌈log_q (k+1)⌉`, so that
`r ≤ vIdx q e k ↔ k < q^(e−r)` (`le_vIdx_iff`). -/
def vIdx (q e : ℕ) (k : Fin (q ^ e)) : Fin (e + 1) := ⟨e - Nat.clog q (k + 1), by omega⟩

theorem le_vIdx_iff {q e : ℕ} (hq : 1 < q) (k : Fin (q ^ e)) {r : ℕ} (hr : r ≤ e) :
    r ≤ (vIdx q e k : ℕ) ↔ (k : ℕ) < q ^ (e - r) := by
  have hc : Nat.clog q (k + 1) ≤ e := (Nat.clog_le_iff_le_pow hq).mpr k.isLt
  have h2 : (k : ℕ) < q ^ (e - r) ↔ Nat.clog q (k + 1) ≤ e - r := by
    rw [Nat.clog_le_iff_le_pow hq]; exact Nat.lt_iff_add_one_le
  rw [h2]
  show r ≤ e - Nat.clog q (k + 1) ↔ _
  omega

/-- Tails of the pushforward of the greedy weights: `P(vIdx ≥ r) = vTail q ν r` for `r ≤ e`. -/
theorem sum_tail_vIdx {q e : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) {r : ℕ} (hr : r ≤ e) :
    ∑ k : Fin (q ^ e), (if r ≤ (vIdx q e k : ℕ) then greedyW ν (q ^ e) k / ((q ^ e : ℕ) : ℝ) else 0)
      = vTail q ν r := by
  have hM : q ^ (e - r) ≤ q ^ e := Nat.pow_le_pow_right (by omega) (Nat.sub_le e r)
  calc _ = ∑ k : Fin (q ^ e), (fun m : ℕ => if m < q ^ (e - r) then
          greedyW ν (q ^ e) m / ((q ^ e : ℕ) : ℝ) else 0) (k : ℕ) :=
        sum_congr rfl fun k _ => by simp only [le_vIdx_iff hq k hr]
    _ = ∑ m ∈ range (q ^ e), (if m < q ^ (e - r) then
          greedyW ν (q ^ e) m / ((q ^ e : ℕ) : ℝ) else 0) :=
        Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < q ^ (e - r) then
          greedyW ν (q ^ e) m / ((q ^ e : ℕ) : ℝ) else 0) (q ^ e)
    _ = ∑ m ∈ range (q ^ (e - r)), greedyW ν (q ^ e) m / ((q ^ e : ℕ) : ℝ) := by
        rw [← sum_filter]
        congr 1
        ext m; simp only [mem_filter, mem_range]; omega
    _ = vTail q ν r := by
        rw [← sum_div, sum_range_greedyW hν, vTail]
        have hQ : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
        have hpow : ((q : ℝ) ^ e) = (q : ℝ) ^ (e - r) * (q : ℝ) ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hr]
        push_cast
        rw [← min_div_div_right (by positivity), div_self (by positivity), min_comm, hpow]
        congr 1
        field_simp

/-- Fibres of the pushforward of the greedy weights: `P(vIdx = r) = vLaw q ν e r`. -/
theorem sum_fiber_vIdx {q e : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) (r : Fin (e + 1)) :
    ∑ k ∈ univ.filter (fun k => vIdx q e k = r), greedyW ν (q ^ e) k / ((q ^ e : ℕ) : ℝ)
      = vLaw q ν e r := by
  rw [sum_filter]
  have hsplit : ∀ k : Fin (q ^ e),
      (if vIdx q e k = r then greedyW ν (q ^ e) k / ((q ^ e : ℕ) : ℝ) else 0)
        = (if (r : ℕ) ≤ (vIdx q e k : ℕ) then greedyW ν (q ^ e) k / ((q ^ e : ℕ) : ℝ) else 0)
          - (if (r : ℕ) + 1 ≤ (vIdx q e k : ℕ) then
              greedyW ν (q ^ e) k / ((q ^ e : ℕ) : ℝ) else 0) := by
    intro k
    simp only [Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | ring1
  have hr : (r : ℕ) ≤ e := Nat.lt_succ_iff.mp r.isLt
  rw [sum_congr rfl fun k _ => hsplit k, sum_sub_distrib, sum_tail_vIdx hq hν hr, vLaw]
  split_ifs with h
  · rw [sum_tail_vIdx hq hν (by omega : (r : ℕ) + 1 ≤ e)]
  · have hre : (r : ℕ) = e := by omega
    rw [hre, sub_eq_self]
    refine sum_eq_zero fun k _ => ?_
    have := (vIdx q e k).isLt
    rw [ite_eq_right (by omega)]

/-- Pushforward of a product weight under a coordinatewise map. -/
theorem sum_pi_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : ι → Type*}
    [∀ j, Fintype (A j)] [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    (V : (j : ι) → A j → B j) (α : (j : ι) → A j → ℝ) (g : ((j : ι) → B j) → ℝ) :
    ∑ k : (j : ι) → A j, (∏ j, α j (k j)) * g (fun j => V j (k j))
      = ∑ v : (j : ι) → B j, (∏ j, ∑ a ∈ univ.filter (fun a => V j a = v j), α j a) * g v := by
  simp_rw [prod_univ_sum, sum_mul]
  rw [← sum_fiberwise univ (fun k : (j : ι) → A j => fun j => V j (k j))]
  refine sum_congr rfl fun v _ => ?_
  have hset : univ.filter (fun k : (j : ι) → A j => (fun j => V j (k j)) = v)
      = Fintype.piFinset (fun j => univ.filter (fun a => V j a = v j)) := by
    ext k; simp [Fintype.mem_piFinset, funext_iff]
  rw [hset]
  refine sum_congr rfl fun k hk => ?_
  have hk' : (fun j => V j (k j)) = v := by
    funext j
    have := Fintype.mem_piFinset.mp hk j
    simpa using this
  rw [hk']

/-- The V-law identity with the sizes `N` and the rectangle cardinalities `b` as variables. -/
theorem aligned_eq_vLaw_aux {n : ℕ} (ν : Fin n → ℝ) (hν : ∀ j, 0 ≤ ν j) (q e : Fin n → ℕ)
    (hq : ∀ j, 1 < q j) {I : Type*} [Fintype I] (w : I → ℝ) (a : I → Fin n → ℕ)
    (ha : ∀ c j, a c j ≤ e j) (t : ℝ)
    (N : Fin n → ℕ) (hN : ∀ j, N j = q j ^ e j)
    (b : I → Fin n → ℕ) (hb : ∀ c j, b c j = q j ^ (e j - a c j)) :
    ∑ k : (j : Fin n) → Fin (N j), (∏ j, greedyW (ν j) (N j) (k j) / N j) *
        max 0 (∑ c, (if ∀ j, (k j : ℕ) < b c j then w c else 0) - t)
      = ∑ v : (j : Fin n) → Fin (e j + 1), (∏ j, vLaw (q j) (ν j) (e j) (v j)) *
        max 0 (∑ c, (if ∀ j, a c j ≤ (v j : ℕ) then w c else 0) - t) := by
  obtain rfl : N = fun j => q j ^ e j := funext hN
  obtain rfl : b = fun c j => q j ^ (e j - a c j) := funext fun c => funext (hb c)
  beta_reduce
  have step1 : ∀ k : (j : Fin n) → Fin (q j ^ e j),
      max 0 (∑ c, (if ∀ j, (k j : ℕ) < q j ^ (e j - a c j) then w c else 0) - t)
        = max 0 (∑ c, (if ∀ j, a c j ≤ (vIdx (q j) (e j) (k j) : ℕ) then w c else 0) - t) := by
    intro k
    congr 2
    refine sum_congr rfl fun c _ => ?_
    by_cases h : ∀ j, (k j : ℕ) < q j ^ (e j - a c j)
    · rw [ite_eq_left h, ite_eq_left (fun j => (le_vIdx_iff (hq j) (k j) (ha c j)).mpr (h j))]
    · rw [ite_eq_right h, ite_eq_right
        (fun h' => h (fun j => (le_vIdx_iff (hq j) (k j) (ha c j)).mp (h' j)))]
  calc _ = ∑ k : (j : Fin n) → Fin (q j ^ e j),
        (∏ j, greedyW (ν j) (q j ^ e j) (k j) / ((q j ^ e j : ℕ) : ℝ)) *
        max 0 (∑ c, (if ∀ j, a c j ≤ (vIdx (q j) (e j) (k j) : ℕ) then w c else 0) - t) :=
        sum_congr rfl fun k _ => by rw [step1]
    _ = ∑ v : (j : Fin n) → Fin (e j + 1),
        (∏ j, ∑ x ∈ univ.filter (fun x => vIdx (q j) (e j) x = v j),
          greedyW (ν j) (q j ^ e j) x / ((q j ^ e j : ℕ) : ℝ)) *
        max 0 (∑ c, (if ∀ j, a c j ≤ (v j : ℕ) then w c else 0) - t) :=
        sum_pi_pushforward (fun j => vIdx (q j) (e j))
          (fun j x => greedyW (ν j) (q j ^ e j) x / ((q j ^ e j : ℕ) : ℝ))
          (fun v => max 0 (∑ c, (if ∀ j, a c j ≤ (v j : ℕ) then w c else 0) - t))
    _ = _ := by
        refine sum_congr rfl fun v _ => ?_
        congr 1
        exact prod_congr rfl fun j _ => sum_fiber_vIdx (hq j) (hν j) (v j)

/-- **V-law corollary.** If `N_j = q_j^{e_j}` and `|S c j| = q_j^{e_j − a c j}` (`a c j ≤ e_j`),
the aligned side of `comparison` equals `E_V[(∑_c w_c [∀ j, a c j ≤ V_j] − t)^+]`, where the
`V_j ∈ {0, …, e_j}` are independent with `P(V_j = r) = vLaw (q j) (ν j) (e j) r`, i.e.
`P(V_j ≥ r) = min 1 (ν_j q_j^{-r})` for `r ≤ e_j`. -/
theorem aligned_eq_vLaw {n : ℕ} {X : Fin n → Type u} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (ν : Fin n → ℝ) (hν : ∀ j, 0 ≤ ν j) (q e : Fin n → ℕ) (hq : ∀ j, 1 < q j)
    (hX : ∀ j, Fintype.card (X j) = q j ^ e j)
    {I : Type v} [Fintype I] (w : I → ℝ) (S : I → (j : Fin n) → Finset (X j))
    (a : I → Fin n → ℕ) (ha : ∀ c j, a c j ≤ e j)
    (hS : ∀ c j, (S c j).card = q j ^ (e j - a c j)) (t : ℝ) :
    ∑ k : (j : Fin n) → Fin (Fintype.card (X j)),
          (∏ j, greedyW (ν j) (Fintype.card (X j)) (k j) / Fintype.card (X j)) *
            max 0 (∑ c, (if ∀ j, (k j : ℕ) < (S c j).card then w c else 0) - t)
      = ∑ v : (j : Fin n) → Fin (e j + 1), (∏ j, vLaw (q j) (ν j) (e j) (v j)) *
            max 0 (∑ c, (if ∀ j, a c j ≤ (v j : ℕ) then w c else 0) - t) :=
  aligned_eq_vLaw_aux ν hν q e hq w a ha t (fun j => Fintype.card (X j)) hX
    (fun c j => (S c j).card) hS

/-- **Comparison theorem, V-law form**: `comparison` followed by `aligned_eq_vLaw`. -/
theorem comparison_vLaw {n : ℕ} {X : Fin n → Type u} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (K : (j : Fin n) → ((i : Fin n) → X i) → X j → ℝ) (ν : Fin n → ℝ)
    (hK0 : ∀ j x y, 0 ≤ K j x y) (hK1 : ∀ j x, ∑ y, K j x y = 1)
    (hKν : ∀ j x y, K j x y ≤ ν j / Fintype.card (X j)) (hν : ∀ j, 1 ≤ ν j)
    (hKdep : ∀ j x x', (∀ i, i < j → x i = x' i) → K j x = K j x')
    (q e : Fin n → ℕ) (hq : ∀ j, 1 < q j) (hX : ∀ j, Fintype.card (X j) = q j ^ e j)
    {I : Type v} [Fintype I] (w : I → ℝ) (hw : ∀ c, 0 ≤ w c)
    (S : I → (j : Fin n) → Finset (X j))
    (a : I → Fin n → ℕ) (ha : ∀ c j, a c j ≤ e j)
    (hS : ∀ c j, (S c j).card = q j ^ (e j - a c j)) (t : ℝ) :
    ∑ x : (j : Fin n) → X j, (∏ j, K j x (x j)) *
        max 0 (∑ c, (if ∀ j, x j ∈ S c j then w c else 0) - t)
      ≤ ∑ v : (j : Fin n) → Fin (e j + 1), (∏ j, vLaw (q j) (ν j) (e j) (v j)) *
            max 0 (∑ c, (if ∀ j, a c j ≤ (v j : ℕ) then w c else 0) - t) :=
  (comparison K ν hK0 hK1 hKν hν hKdep w hw S t).trans_eq
    (aligned_eq_vLaw ν (fun j => by linarith [hν j]) q e hq hX w S a ha hS t)

/-! ## Facts about the V-law -/

theorem vTail_zero (q : ℕ) {ν : ℝ} (hν : 1 ≤ ν) : vTail q ν 0 = 1 := by
  rw [vTail, pow_zero, div_one, min_eq_left hν]

theorem vTail_of_one_le {q : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hνq : ν ≤ q) {r : ℕ} (hr : 1 ≤ r) :
    vTail q ν r = ν / (q : ℝ) ^ r := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < (q : ℝ) ^ r := pow_pos (by linarith) r
  rw [vTail, min_eq_right]
  rw [div_le_one hpos]
  calc ν ≤ q := hνq
    _ = (q : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (q : ℝ) ^ r := pow_le_pow_right₀ hq' hr

/-- For `1 ≤ ν ≤ q`, `vTail q ν r = if r = 0 then 1 else ν * (q⁻¹)^r` (the body of
`MinModulus.Smooth.tailP`). -/
theorem vTail_eq_ite {q : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hν : 1 ≤ ν) (hνq : ν ≤ q) (r : ℕ) :
    vTail q ν r = if r = 0 then 1 else ν * ((q : ℝ)⁻¹) ^ r := by
  split_ifs with h
  · subst h; exact vTail_zero q hν
  · rw [vTail_of_one_le hq hνq (Nat.one_le_iff_ne_zero.mpr h), inv_pow, div_eq_mul_inv]

theorem vTail_succ_le {q : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hν : 0 ≤ ν) (r : ℕ) :
    vTail q ν (r + 1) ≤ vTail q ν r := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  unfold vTail
  refine min_le_min le_rfl (div_le_div_of_nonneg_left hν (pow_pos (by linarith) r) ?_)
  exact pow_le_pow_right₀ hq' (Nat.le_succ r)

/-- The V-law probabilities are nonnegative (needs only `1 ≤ q` and `0 ≤ ν`). -/
theorem vLaw_nonneg {q : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hν : 0 ≤ ν) (e r : ℕ) :
    0 ≤ vLaw q ν e r := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold vLaw
  split_ifs
  · linarith [vTail_succ_le hq hν r]
  · exact le_min zero_le_one (div_nonneg hν (pow_pos hq' e).le)

/-- The product V-law weight is nonnegative (for `gcongr` side goals). -/
theorem prod_vLaw_nonneg {n : ℕ} (q e : Fin n → ℕ) (ν : Fin n → ℝ) (hq : ∀ j, 1 ≤ q j)
    (hν : ∀ j, 0 ≤ ν j) (v : (j : Fin n) → Fin (e j + 1)) :
    0 ≤ ∏ j, vLaw (q j) (ν j) (e j) (v j) :=
  prod_nonneg fun j _ => vLaw_nonneg (hq j) (hν j) _ _

/-- The V-law is a probability law on `{0, …, e}`. -/
theorem sum_vLaw (q : ℕ) {ν : ℝ} (hν : 1 ≤ ν) (e : ℕ) :
    ∑ r : Fin (e + 1), vLaw q ν e r = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => vLaw q ν e r) (e + 1), sum_range_succ]
  have h1 : ∑ r ∈ range e, vLaw q ν e r = ∑ r ∈ range e, (vTail q ν r - vTail q ν (r + 1)) :=
    sum_congr rfl fun r hr => by rw [vLaw, ite_eq_left (mem_range.mp hr)]
  rw [h1, sum_range_sub', vLaw, ite_eq_right (lt_irrefl e), vTail_zero q hν]
  ring

/-- Explicit values (matching `Smooth.rho`), for `1 ≤ ν ≤ q`: cap `e = 0`. -/
theorem vLaw_cap_zero (q : ℕ) {ν : ℝ} (hν : 1 ≤ ν) : vLaw q ν 0 0 = 1 := by
  rw [vLaw, ite_eq_right (lt_irrefl 0), vTail_zero q hν]

/-- Explicit values: `P(V = 0) = 1 − ν/q` when `e ≥ 1`. -/
theorem vLaw_zero {q e : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hν : 1 ≤ ν) (hνq : ν ≤ q) (he : 1 ≤ e) :
    vLaw q ν e 0 = 1 - ν / q := by
  rw [vLaw, ite_eq_left (by omega), vTail_zero q hν, vTail_of_one_le hq hνq le_rfl, pow_one]

/-- Explicit values: `P(V = r) = ν q^{-r} (1 − 1/q)` for `1 ≤ r < e`. -/
theorem vLaw_mid {q e r : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hνq : ν ≤ q) (hr : 1 ≤ r) (hre : r < e) :
    vLaw q ν e r = ν / (q : ℝ) ^ r * (1 - 1 / q) := by
  have hq' : (q : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    positivity
  rw [vLaw, ite_eq_left hre, vTail_of_one_le hq hνq hr, vTail_of_one_le hq hνq (by omega),
    pow_succ]
  field_simp

/-- Explicit values: `P(V ≥ e) = ν q^{-e}` for `e ≥ 1`. -/
theorem vLaw_top {q e : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hνq : ν ≤ q) (he : 1 ≤ e) :
    vLaw q ν e e = ν / (q : ℝ) ^ e := by
  rw [vLaw, ite_eq_right (lt_irrefl e), vTail_of_one_le hq hνq he]

end MinModulus.Comparison
