import MinModulus.Checker2Math.Laws
import MinModulus.Checker2Math.Identities

/-!
# `Checker2Math.SBHLaw`: the joint law of `(T, b)` and the lower-tail leaf bound (L2-A)

STATUS: complete (fully proved; lean2 stage 2, agent L2-A). Every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`.

Setting: a finite set `R` (the `B ∪ H` primes of the S/B/H bound), a profile `a : ℕ → ℕ`
(`a_q(s_S)` on `B`, `0` on `H`), tilts `ν`, caps `γ`, under Smooth's capped tilted product law.
`T = tauN R w = ∏_{q ∈ R} (w q + 1)`, `b = bstat R a w = Σ_{q ∈ R, w q ≥ 1} a q`,
`lawJoint R a ν γ k j = P(T = k ∧ b = j)` (`Checker2Math.Laws`). All identities hold for
**every** cap `γ`.

## Results
* `bstat`: `bstat_empty`, `bstat_le_sum`, `bstat_update_of_notMem`, `bstat_insert_update`,
  `bstat_congr`, `bstat_eq_zero`.
* `lawJoint` basics: `lawJoint_nonneg`, `lawJoint_zero_left` (`T ≥ 1`), `lawJoint_of_sum_lt`
  (`b ≤ Σ a`), `lawJoint_empty`, `lawJoint_congr`, `lawJoint_eq_lawTau` (profile `0` on `R`).
* **The DP step** (exact, every cap, `q ∉ R`): `lawJoint_insert` (pull form),
  `lawJoint_insert_split` (the `x = 0` / `x ≥ 1` split of `rowsStep`), `lawJoint_insert_push`
  (push form on `[0, K]`, the form of `dpRange`), and the rounded `lawJoint_insert_le`.
* Moments: `expect_bstat` (`E[b] = Σ_{q ∈ R} a q ν_q/q` for caps `≥ 1`),
  `expect_eq_sum_lawJoint` (`E[Φ(T, b)] = Σ_b Σ_k Φ(k, b) P(T = k, b)`).
* **The lower-tail leaf bound**: `sbhLeaf R ν γ a τ β ω = E_R[(τ T − β − ω b)⁺]`;
  `sbhLeaf_eq` (the exact lower-tail identity), `sbhLeaf_le` (with lower bounds `β' ≤ β`,
  `ω' ≤ ω`, `ET ≥ E[T]`, `Eb ≤ E[b]` and any `c_b ≥ (β' + ω' b)/τ`: the form computed by
  `SBH.leafValue`/`corrSum`), `sbhLeaf_anti`, `sbhLeaf_nonneg`, `sbhLeaf_le_mul`,
  `sbhLeaf_le_prod` (the DFS pruning input), `sbhLeaf_congr`, and `lowerTail_row_eq_zero`
  (rows with `c_b < 1` contribute `0`: `corrSum`'s skip). Row-sum algebra: `max_sub_mul_eq`,
  `lowerTail_eq_sum_max`, `lowerTail_mono`.
-/

namespace MinModulus.Checker2Math.A

open Finset MinModulus.Smooth MinModulus.CheckerMath MinModulus.Checker2Math

/-! ## The statistic `b` -/

@[simp] theorem bstat_empty (a w : ℕ → ℕ) : bstat ∅ a w = 0 := by
  simp [bstat]

/-- `b ≤ Σ_{q ∈ R} a q`. -/
theorem bstat_le_sum (R : Finset ℕ) (a w : ℕ → ℕ) : bstat R a w ≤ ∑ q ∈ R, a q := by
  unfold bstat
  exact sum_le_sum fun q _ => by split_ifs <;> omega

theorem bstat_update_of_notMem {q : ℕ} {R : Finset ℕ} (hq : q ∉ R) (a w : ℕ → ℕ) (x : ℕ) :
    bstat R a (Function.update w q x) = bstat R a w := by
  unfold bstat
  refine sum_congr rfl fun r hr => ?_
  rw [Function.update_of_ne (ne_of_mem_of_not_mem hr hq)]

/-- Adding `q ∉ R` with exponent `x` adds `a q` to `b` iff `x ≥ 1`. -/
theorem bstat_insert_update {q : ℕ} {R : Finset ℕ} (hq : q ∉ R) (a w : ℕ → ℕ) (x : ℕ) :
    bstat (insert q R) a (Function.update w q x) = (if 1 ≤ x then a q else 0) + bstat R a w := by
  rw [← bstat_update_of_notMem hq a w x]
  unfold bstat
  rw [sum_insert hq, Function.update_self]

/-- `b` depends on `a` only through its values on `R`. -/
theorem bstat_congr {R : Finset ℕ} {a a' : ℕ → ℕ} (h : ∀ q ∈ R, a q = a' q) (w : ℕ → ℕ) :
    bstat R a w = bstat R a' w := by
  unfold bstat
  exact sum_congr rfl fun q hq => by rw [h q hq]

theorem bstat_eq_zero {R : Finset ℕ} {a : ℕ → ℕ} (h : ∀ q ∈ R, a q = 0) (w : ℕ → ℕ) :
    bstat R a w = 0 := by
  unfold bstat
  exact sum_eq_zero fun q hq => by simp [h q hq]

/-! ## `lawJoint`: basic facts -/

theorem lawJoint_nonneg {R : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ R, 0 ≤ ν q ∧ ν q ≤ q)
    (a : ℕ → ℕ) (γ : ℕ → ℕ) (k j : ℕ) : 0 ≤ lawJoint R a ν γ k j :=
  expect_nonneg hν fun v _ => by split_ifs <;> norm_num

/-- `T ≥ 1`: no mass at `T = 0`. -/
theorem lawJoint_zero_left (R : Finset ℕ) (a : ℕ → ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (j : ℕ) :
    lawJoint R a ν γ 0 j = 0 := by
  unfold lawJoint
  refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const R ν γ 0)
  have : ¬ (tauN R v = 0 ∧ bstat R a v = j) := fun h => (tauN_pos R v).ne' h.1
  simp [this]

/-- `b ≤ Σ_{q ∈ R} a q`: no mass beyond. -/
theorem lawJoint_of_sum_lt (R : Finset ℕ) (a : ℕ → ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (k : ℕ) {j : ℕ}
    (hj : ∑ q ∈ R, a q < j) : lawJoint R a ν γ k j = 0 := by
  unfold lawJoint
  refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const R ν γ 0)
  have : ¬ (tauN R v = k ∧ bstat R a v = j) := fun h => by
    have := bstat_le_sum R a v
    omega
  simp [this]

/-- The empty product: `T = 1`, `b = 0` surely. -/
theorem lawJoint_empty (a : ℕ → ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (k j : ℕ) :
    lawJoint ∅ a ν γ k j = if k = 1 ∧ j = 0 then 1 else 0 := by
  unfold lawJoint
  rw [expect_empty, tauN_empty, bstat_empty]
  by_cases h : k = 1 ∧ j = 0
  · rw [ite_eq_left ⟨h.1.symm, h.2.symm⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), ite_eq_right h]

/-- `lawJoint R a` depends on `a` only through its values on `R`. -/
theorem lawJoint_congr {R : Finset ℕ} {a a' : ℕ → ℕ} (h : ∀ q ∈ R, a q = a' q) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) (k j : ℕ) : lawJoint R a ν γ k j = lawJoint R a' ν γ k j := by
  unfold lawJoint
  exact expect_congr_fun fun v _ => by rw [bstat_congr h]

/-- A zero profile (the `H` part alone): `P(T = k ∧ b = j) = [j = 0]·P(T = k)`. -/
theorem lawJoint_eq_lawTau {R : Finset ℕ} {a : ℕ → ℕ} (h : ∀ q ∈ R, a q = 0) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) (k j : ℕ) : lawJoint R a ν γ k j = if j = 0 then lawTau R ν γ k else 0 := by
  unfold lawJoint lawTau
  split_ifs with hj
  · subst hj
    exact expect_congr_fun fun v _ => by simp [bstat_eq_zero h]
  · refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const R ν γ 0)
    have : ¬ (tauN R v = k ∧ bstat R a v = j) := fun h' => hj (by rw [← h'.2, bstat_eq_zero h])
    simp [this]

/-! ## The DP step -/

/-- Pointwise form of the DP step. -/
theorem ind_joint_insert_update {q : ℕ} {R : Finset ℕ} (hq : q ∉ R) (a w : ℕ → ℕ) (x k j : ℕ) :
    (if tauN (insert q R) (Function.update w q x) = k ∧
        bstat (insert q R) a (Function.update w q x) = j then (1 : ℝ) else 0) =
      if (x + 1) ∣ k ∧ (x = 0 ∨ a q ≤ j) then
        (if tauN R w = k / (x + 1) ∧ bstat R a w = (if x = 0 then j else j - a q) then 1 else 0)
      else 0 := by
  rw [tauN_insert_update hq, bstat_insert_update hq]
  by_cases h1 : (x + 1) ∣ k ∧ (x = 0 ∨ a q ≤ j)
  · rw [ite_eq_left h1]
    obtain ⟨⟨c, rfl⟩, h2⟩ := h1
    rw [Nat.mul_div_cancel_left _ (Nat.succ_pos x)]
    have e : (tauN R w * (x + 1) = (x + 1) * c ∧ (if 1 ≤ x then a q else 0) + bstat R a w = j) ↔
        (tauN R w = c ∧ bstat R a w = (if x = 0 then j else j - a q)) := by
      have e1 : tauN R w * (x + 1) = (x + 1) * c ↔ tauN R w = c := by
        rw [mul_comm]
        exact ⟨fun h => Nat.eq_of_mul_eq_mul_left (Nat.succ_pos x) h, fun h => by rw [h]⟩
      rw [e1]
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx
        simp
      · have hx1 : 1 ≤ x := hx
        have hx0 : x ≠ 0 := by omega
        simp only [hx1, ↓reduceIte, hx0]
        rcases h2 with h2 | h2
        · omega
        · constructor
          · rintro ⟨h3, h4⟩; exact ⟨h3, by omega⟩
          · rintro ⟨h3, h4⟩; exact ⟨h3, by omega⟩
    by_cases h3 : tauN R w = c ∧ bstat R a w = (if x = 0 then j else j - a q)
    · rw [ite_eq_left (e.2 h3), ite_eq_left h3]
    · rw [ite_eq_right (fun h => h3 (e.1 h)), ite_eq_right h3]
  · rw [ite_eq_right h1, ite_eq_right]
    rintro ⟨h3, h4⟩
    apply h1
    refine ⟨⟨tauN R w, by rw [← h3, mul_comm]⟩, ?_⟩
    rcases Nat.eq_zero_or_pos x with hx | hx
    · exact Or.inl hx
    · right
      have hx1 : 1 ≤ x := hx
      simp only [hx1, ↓reduceIte] at h4
      omega

/-- **The DP step, pull form** (exact, every cap): for `q ∉ R`,
`P_{R ∪ {q}}(T = k, b = j) = Σ_{x ≤ γ q, (x+1) ∣ k, x = 0 ∨ a q ≤ j}
  ρ_q(x)·P_R(T = k/(x+1), b = j − [x ≥ 1] a q)`. -/
theorem lawJoint_insert {q : ℕ} {R : Finset ℕ} (hq : q ∉ R) (a : ℕ → ℕ) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) (k j : ℕ) :
    lawJoint (insert q R) a ν γ k j =
      ∑ x ∈ range (γ q + 1), if (x + 1) ∣ k ∧ (x = 0 ∨ a q ≤ j) then
        rho q (ν q) (γ q) x * lawJoint R a ν γ (k / (x + 1)) (if x = 0 then j else j - a q)
      else 0 := by
  unfold lawJoint
  rw [expect_insert hq]
  refine sum_congr rfl fun x _ => ?_
  simp_rw [ind_joint_insert_update hq a _ x k j]
  split_ifs
  · rfl
  · rfl
  · rw [expect_const, mul_zero]

/-- **The DP step, split form** (`rowsStep`: exponent `0` keeps the row, exponents `≥ 1` shift
the row by `a q`). -/
theorem lawJoint_insert_split {q : ℕ} {R : Finset ℕ} (hq : q ∉ R) (a : ℕ → ℕ) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) (k j : ℕ) :
    lawJoint (insert q R) a ν γ k j =
      rho q (ν q) (γ q) 0 * lawJoint R a ν γ k j +
      (if a q ≤ j then ∑ x ∈ Ico 1 (γ q + 1), if (x + 1) ∣ k then
          rho q (ν q) (γ q) x * lawJoint R a ν γ (k / (x + 1)) (j - a q) else 0
        else 0) := by
  rw [lawJoint_insert hq, range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
  congr 1
  · simp
  · split_ifs with h
    · refine sum_congr rfl fun x hx => ?_
      have hx0 : x ≠ 0 := by have := (mem_Ico.1 hx).1; omega
      simp [hx0, h]
    · refine sum_eq_zero fun x hx => ?_
      have hx0 : x ≠ 0 := by have := (mem_Ico.1 hx).1; omega
      simp [hx0, h]

/-- **The DP step, push form on `[0, K]`** (the form of `dpRange`): for `q ∉ R` and `T ≤ K`
(every cap; exponents `x ≥ K` cannot reach `T ≤ K`). -/
theorem lawJoint_insert_push {q : ℕ} {R : Finset ℕ} (hq : q ∉ R) (a : ℕ → ℕ) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) {K T : ℕ} (hT : T ≤ K) (j : ℕ) :
    lawJoint (insert q R) a ν γ T j =
      rho q (ν q) (γ q) 0 * lawJoint R a ν γ T j +
      (if a q ≤ j then ∑ t ∈ range (K + 1), ∑ x ∈ Ico 1 K, if t * (x + 1) = T then
          rho q (ν q) (γ q) x * lawJoint R a ν γ t (j - a q) else 0
        else 0) := by
  rw [lawJoint_insert_split hq]
  congr 1
  split_ifs with h
  · symm
    rw [sum_comm]
    have e1 : ∀ x ∈ Ico 1 K, ∑ t ∈ range (K + 1), (if t * (x + 1) = T then
        rho q (ν q) (γ q) x * lawJoint R a ν γ t (j - a q) else 0) =
        if (x + 1) ∣ T then rho q (ν q) (γ q) x * lawJoint R a ν γ (T / (x + 1)) (j - a q)
        else 0 :=
      fun x _ => sum_mul_succ_eq hT x (fun t => rho q (ν q) (γ q) x * lawJoint R a ν γ t (j - a q))
    rw [sum_congr rfl e1]
    have hvan : ∀ x, (K ≤ x ∨ γ q < x) → (if (x + 1) ∣ T then
        rho q (ν q) (γ q) x * lawJoint R a ν γ (T / (x + 1)) (j - a q) else 0) = 0 := by
      intro x hx
      split_ifs with hd
      · rcases hx with hx | hx
        · have hT0 : T = 0 := by
            rcases Nat.eq_zero_or_pos T with h0 | h0
            · exact h0
            · exact absurd (Nat.le_of_dvd h0 hd) (by omega)
          subst hT0
          rw [Nat.zero_div, lawJoint_zero_left, mul_zero]
        · rw [rho_of_gt hx, zero_mul]
      · rfl
    have hA : ∑ x ∈ Ico 1 (γ q + 1), (if (x + 1) ∣ T then
        rho q (ν q) (γ q) x * lawJoint R a ν γ (T / (x + 1)) (j - a q) else 0) =
        ∑ x ∈ Ico 1 (γ q + 1 + K), (if (x + 1) ∣ T then
        rho q (ν q) (γ q) x * lawJoint R a ν γ (T / (x + 1)) (j - a q) else 0) := by
      refine sum_subset (Ico_subset_Ico_right (by omega)) fun x hx hnx => hvan x ?_
      simp only [mem_Ico, not_and, not_lt] at hx hnx
      right
      have := hnx hx.1
      omega
    have hB : ∑ x ∈ Ico 1 K, (if (x + 1) ∣ T then
        rho q (ν q) (γ q) x * lawJoint R a ν γ (T / (x + 1)) (j - a q) else 0) =
        ∑ x ∈ Ico 1 (γ q + 1 + K), (if (x + 1) ∣ T then
        rho q (ν q) (γ q) x * lawJoint R a ν γ (T / (x + 1)) (j - a q) else 0) := by
      refine sum_subset (Ico_subset_Ico_right (by omega)) fun x hx hnx => hvan x ?_
      simp only [mem_Ico, not_and, not_lt] at hx hnx
      left
      exact hnx hx.1
    rw [hA, hB]
  · rfl

/-- **The DP step with upper bounds** (push form): `D t i ≥ P_R(T = t, b = i)` for `t ≤ K`,
`i ≤ j`, and `ℓ x ≥ ρ_q(x)` for `x < K` give an upper bound of `P_{R ∪ {q}}(T = T₀, b = j)`,
`T₀ ≤ K`. -/
theorem lawJoint_insert_le {q : ℕ} {R : Finset ℕ} (hq : q ∉ R) {ν : ℕ → ℝ}
    (hν : ∀ r ∈ insert q R, 0 ≤ ν r ∧ ν r ≤ r) (a : ℕ → ℕ) (γ : ℕ → ℕ) {K : ℕ} (hK : 0 < K)
    (D : ℕ → ℕ → ℝ) (ℓ : ℕ → ℝ) {j : ℕ}
    (hD : ∀ t ≤ K, ∀ i ≤ j, lawJoint R a ν γ t i ≤ D t i)
    (hℓ : ∀ x < K, rho q (ν q) (γ q) x ≤ ℓ x) {T : ℕ} (hT : T ≤ K) :
    lawJoint (insert q R) a ν γ T j ≤
      ℓ 0 * D T j +
      (if a q ≤ j then ∑ t ∈ range (K + 1), ∑ x ∈ Ico 1 K, if t * (x + 1) = T then
          ℓ x * D t (j - a q) else 0
        else 0) := by
  rw [lawJoint_insert_push hq a ν γ hT j]
  have hνR : ∀ r ∈ R, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
  have hνq := hν q (mem_insert_self q R)
  have hρ0 : ∀ x, 0 ≤ rho q (ν q) (γ q) x := fun x => rho_nonneg hνq.1 hνq.2 _ _
  have hL0 : ∀ t i, 0 ≤ lawJoint R a ν γ t i := fun t i => lawJoint_nonneg hνR a γ t i
  refine add_le_add ?_ ?_
  · exact mul_le_mul (hℓ 0 hK) (hD T hT j le_rfl) (hL0 T j) ((hρ0 0).trans (hℓ 0 hK))
  · split_ifs with h
    · refine sum_le_sum fun t ht => sum_le_sum fun x hx => ?_
      split_ifs
      · have ht' : t ≤ K := Nat.lt_succ_iff.1 (mem_range.1 ht)
        have hx' : x < K := (mem_Ico.1 hx).2
        exact mul_le_mul (hℓ x hx') (hD t ht' _ (Nat.sub_le j (a q))) (hL0 _ _)
          ((hρ0 x).trans (hℓ x hx'))
      · exact le_rfl
    · exact le_rfl

/-! ## Moments -/

/-- `E[b] = Σ_{q ∈ R} a q · ν_q/q` for caps `≥ 1` (`P(v_q ≥ 1) = ν_q/q`). -/
theorem expect_bstat {R : Finset ℕ} {γ : ℕ → ℕ} (hγ : ∀ q ∈ R, 1 ≤ γ q) (a : ℕ → ℕ)
    (ν : ℕ → ℝ) :
    expect R ν γ (fun w => (bstat R a w : ℝ)) = ∑ q ∈ R, (a q : ℝ) * (ν q / q) := by
  have hcast : ∀ w : ℕ → ℕ, (bstat R a w : ℝ) =
      ∑ q ∈ R, (fun x => if 1 ≤ x then (a q : ℝ) else 0) (w q) := by
    intro w
    unfold bstat
    push_cast
    rfl
  simp_rw [hcast]
  rw [expect_sum]
  refine sum_congr rfl fun q hq => ?_
  rw [expect_coord hq ν γ (fun x => if 1 ≤ x then (a q : ℝ) else 0)]
  have e : (fun x : ℕ => if 1 ≤ x then (a q : ℝ) else 0) =
      fun x => (a q : ℝ) * (if 1 ≤ x then 1 else 0) := by
    funext x
    split_ifs <;> simp
  rw [e, expect1_const_mul, expect1_indicator (hγ q hq), tailP_of_ne_zero one_ne_zero, pow_one,
    div_eq_mul_inv]

/-- `E[Φ(T, b)] = Σ_{b ≤ M} Σ_{k ≤ K_b} Φ(k, b)·P(T = k, b)` when `Σ_{q ∈ R} a q ≤ M` and
`Φ(k, b) = 0` for `k > K_b`. -/
theorem expect_eq_sum_lawJoint {R : Finset ℕ} {a : ℕ → ℕ} {M : ℕ} (hM : ∑ q ∈ R, a q ≤ M)
    (ν : ℕ → ℝ) (γ : ℕ → ℕ) (Kb : ℕ → ℕ) (Φ : ℕ → ℕ → ℝ)
    (hΦ : ∀ b ≤ M, ∀ k, Kb b < k → Φ k b = 0) :
    expect R ν γ (fun w => Φ (tauN R w) (bstat R a w)) =
      ∑ b ∈ range (M + 1), ∑ k ∈ range (Kb b + 1), Φ k b * lawJoint R a ν γ k b := by
  have hpt : ∀ w : ℕ → ℕ, Φ (tauN R w) (bstat R a w) =
      ∑ b ∈ range (M + 1), ∑ k ∈ range (Kb b + 1),
        Φ k b * (if tauN R w = k ∧ bstat R a w = b then (1 : ℝ) else 0) := by
    intro w
    have hb : bstat R a w ≤ M := (bstat_le_sum R a w).trans hM
    rw [sum_eq_single (bstat R a w)]
    · by_cases hk : tauN R w ≤ Kb (bstat R a w)
      · rw [sum_eq_single (tauN R w)]
        · simp
        · intro k _ hk'
          have : ¬ (tauN R w = k ∧ bstat R a w = bstat R a w) := fun h => hk' h.1.symm
          rw [ite_eq_right this, mul_zero]
        · intro h
          exact absurd (mem_range.2 (Nat.lt_succ_of_le hk)) h
      · rw [hΦ _ hb _ (not_le.1 hk)]
        refine (sum_eq_zero fun k hk' => ?_).symm
        have : ¬ (tauN R w = k ∧ bstat R a w = bstat R a w) := fun h => by
          have := Nat.lt_succ_iff.1 (mem_range.1 hk')
          omega
        rw [ite_eq_right this, mul_zero]
    · intro b _ hb'
      refine sum_eq_zero fun k _ => ?_
      have : ¬ (tauN R w = k ∧ bstat R a w = b) := fun h => hb' h.2.symm
      rw [ite_eq_right this, mul_zero]
    · intro h
      exact absurd (mem_range.2 (Nat.lt_succ_of_le hb)) h
  rw [show (fun w => Φ (tauN R w) (bstat R a w)) = fun w => ∑ b ∈ range (M + 1),
      ∑ k ∈ range (Kb b + 1), Φ k b * (if tauN R w = k ∧ bstat R a w = b then (1 : ℝ) else 0)
    from funext hpt, expect_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [expect_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [expect_const_mul]
  rfl

/-! ## The lower-tail leaf bound -/

/-- A term of the lower-tail row sum: for `j ≤ ⌊c⌋₊`, `(c − j)⁺ L j = (c − j) L j` (`L 0 = 0`). -/
theorem max_sub_mul_eq (L : ℕ → ℝ) (hL0 : L 0 = 0) (c : ℝ) {j : ℕ} (hj : j ≤ ⌊c⌋₊) :
    max 0 (c - j) * L j = (c - j) * L j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [hL0]
  · have : (j : ℝ) ≤ c := (Nat.le_floor_iff' (by omega)).1 hj
    rw [max_eq_right (by linarith)]

/-- The lower-tail row sum as a sum of hinges: for `N ≥ ⌊c⌋₊` and `L 0 = 0`,
`Σ_{j ≤ ⌊c⌋₊} (c − j) L j = Σ_{j ≤ N} (c − j)⁺ L j`. -/
theorem lowerTail_eq_sum_max (L : ℕ → ℝ) (hL0 : L 0 = 0) (c : ℝ) {N : ℕ} (hN : ⌊c⌋₊ ≤ N) :
    ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * L j = ∑ j ∈ range (N + 1), max 0 (c - j) * L j := by
  have h1 : ∑ j ∈ range (N + 1), max 0 (c - j) * L j =
      ∑ j ∈ range (⌊c⌋₊ + 1), max 0 (c - j) * L j := by
    refine (sum_subset (range_mono (by omega)) fun j _ hnj => ?_).symm
    have : ⌊c⌋₊ + 1 ≤ j := by simpa using hnj
    have hj' : (⌊c⌋₊ : ℝ) + 1 ≤ j := by exact_mod_cast this
    have := Nat.lt_floor_add_one c
    rw [max_eq_left (by linarith), zero_mul]
  rw [h1]
  exact (sum_congr rfl fun j hj => max_sub_mul_eq L hL0 c (Nat.lt_succ_iff.1 (mem_range.1 hj))).symm

/-- The lower-tail row sum is monotone in `c` (`L ≥ 0`, `L 0 = 0`). -/
theorem lowerTail_mono (L : ℕ → ℝ) (hL0 : L 0 = 0) (hL : ∀ j, 0 ≤ L j) {c c' : ℝ} (h : c' ≤ c) :
    ∑ j ∈ range (⌊c'⌋₊ + 1), (c' - j) * L j ≤ ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * L j := by
  rw [lowerTail_eq_sum_max L hL0 c' (Nat.floor_mono h), lowerTail_eq_sum_max L hL0 c le_rfl]
  exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (max_le_max le_rfl (by linarith)) (hL j)

/-- The S/B/H leaf function `E_R[(τ·T − β − ω·b)⁺]` (`T = tauN R`, `b = bstat R a`). -/
noncomputable def sbhLeaf (R : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (a : ℕ → ℕ) (τ β ω : ℝ) :
    ℝ :=
  expect R ν γ (fun w => max 0 (τ * (tauN R w : ℝ) - β - ω * (bstat R a w : ℝ)))

theorem sbhLeaf_nonneg {R : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ R, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (a : ℕ → ℕ) (τ β ω : ℝ) : 0 ≤ sbhLeaf R ν γ a τ β ω :=
  expect_nonneg hν fun _ _ => le_max_left _ _

theorem sbhLeaf_congr {R : Finset ℕ} {a a' : ℕ → ℕ} (h : ∀ q ∈ R, a q = a' q) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) (τ β ω : ℝ) : sbhLeaf R ν γ a τ β ω = sbhLeaf R ν γ a' τ β ω := by
  unfold sbhLeaf
  exact expect_congr_fun fun w _ => by rw [bstat_congr h]

/-- Lowering the thresholds raises the hinge: `β' ≤ β`, `ω' ≤ ω` (`b ≥ 0`). -/
theorem sbhLeaf_anti {R : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ R, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (a : ℕ → ℕ) (τ : ℝ) {β β' ω ω' : ℝ} (hβ : β' ≤ β) (hω : ω' ≤ ω) :
    sbhLeaf R ν γ a τ β ω ≤ sbhLeaf R ν γ a τ β' ω' := by
  unfold sbhLeaf
  refine expect_mono hν fun w _ => max_le_max le_rfl ?_
  have hb : (0 : ℝ) ≤ bstat R a w := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hω hb]

/-- For nonnegative thresholds, `E_R[(τT − β − ωb)⁺] ≤ τ·E_R[T]` (the DFS pruning input). -/
theorem sbhLeaf_le_mul {R : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ R, 0 ≤ ν q ∧ ν q ≤ q)
    (γ : ℕ → ℕ) (a : ℕ → ℕ) {τ β ω : ℝ} (hτ : 0 ≤ τ) (hβ : 0 ≤ β) (hω : 0 ≤ ω) :
    sbhLeaf R ν γ a τ β ω ≤ τ * expect R ν γ (fun w => (tauN R w : ℝ)) := by
  unfold sbhLeaf
  rw [← expect_const_mul]
  refine expect_mono hν fun w _ => max_le (mul_nonneg hτ (Nat.cast_nonneg _)) ?_
  have hb : (0 : ℝ) ≤ bstat R a w := Nat.cast_nonneg _
  nlinarith [mul_nonneg hω hb]

/-- `E_R[(τT − β − ωb)⁺] ≤ τ·∏_{q ∈ R} (1 + ν_q/(q−1))` for nonnegative thresholds, every cap. -/
theorem sbhLeaf_le_prod {R : Finset ℕ} (hR : ∀ q ∈ R, 1 < q) {ν : ℕ → ℝ}
    (hν : ∀ q ∈ R, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (a : ℕ → ℕ) {τ β ω : ℝ} (hτ : 0 ≤ τ)
    (hβ : 0 ≤ β) (hω : 0 ≤ ω) :
    sbhLeaf R ν γ a τ β ω ≤ τ * ∏ q ∈ R, (1 + ν q / ((q : ℝ) - 1)) :=
  (sbhLeaf_le_mul hν γ a hτ hβ hω).trans
    (mul_le_mul_of_nonneg_left (expect_tauN_le hR (fun q hq => (hν q hq).1) γ) hτ)

/-- **The lower-tail identity** (exact): for `τ > 0` and `Σ_{q ∈ R} a q ≤ M`, with
`c_b = (β + ω b)/τ`:
`E_R[(τT − β − ωb)⁺] = τ E[T] − β − ω E[b] + τ Σ_{b ≤ M} Σ_{j ≤ ⌊c_b⌋} (c_b − j) P(T = j, b)`. -/
theorem sbhLeaf_eq {R : Finset ℕ} {a : ℕ → ℕ} {M : ℕ} (hM : ∑ q ∈ R, a q ≤ M) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) {τ : ℝ} (hτ : 0 < τ) (β ω : ℝ) :
    sbhLeaf R ν γ a τ β ω =
      τ * expect R ν γ (fun w => (tauN R w : ℝ)) - β - ω * expect R ν γ (fun w => (bstat R a w : ℝ))
        + τ * ∑ b ∈ range (M + 1), ∑ j ∈ range (⌊(β + ω * b) / τ⌋₊ + 1),
            ((β + ω * b) / τ - j) * lawJoint R a ν γ j b := by
  unfold sbhLeaf
  rw [expect_hinge_eq]
  have hlin : expect R ν γ (fun w => τ * (tauN R w : ℝ) - β - ω * (bstat R a w : ℝ)) =
      τ * expect R ν γ (fun w => (tauN R w : ℝ)) - β -
        ω * expect R ν γ (fun w => (bstat R a w : ℝ)) := by
    rw [expect_sub, expect_sub, expect_const_mul, expect_const, expect_const_mul]
  rw [hlin]
  congr 1
  have hpt : expect R ν γ (fun w => max 0 (-(τ * (tauN R w : ℝ) - β - ω * (bstat R a w : ℝ)))) =
      expect R ν γ (fun w => (fun (k b : ℕ) => τ * max 0 ((β + ω * (b : ℝ)) / τ - (k : ℝ)))
        (tauN R w) (bstat R a w)) := by
    refine expect_congr_fun fun w _ => ?_
    simp only
    rw [mul_max_of_nonneg _ _ hτ.le, mul_zero, mul_sub, mul_div_cancel₀ _ hτ.ne']
    congr 1
    ring
  rw [hpt, expect_eq_sum_lawJoint hM ν γ (fun b => ⌊(β + ω * (b : ℝ)) / τ⌋₊)
    (fun (k b : ℕ) => τ * max 0 ((β + ω * (b : ℝ)) / τ - (k : ℝ)))]
  · rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mul_assoc, max_sub_mul_eq (fun j => lawJoint R a ν γ j b) (lawJoint_zero_left R a ν γ b)
      _ (Nat.lt_succ_iff.1 (mem_range.1 hj))]
  · intro b _ k hk
    have hk' : (⌊(β + ω * (b : ℝ)) / τ⌋₊ : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have := Nat.lt_floor_add_one ((β + ω * (b : ℝ)) / τ)
    rw [max_eq_left (by linarith), mul_zero]

/-- **The lower-tail leaf bound** (the form computed by `leafValue`/`corrSum`): for `τ > 0`,
lower bounds `β' ≤ β`, `0 ≤ ω' ≤ ω` of the thresholds, `ET ≥ E[T]`, `Eb ≤ E[b]`,
`Σ_{q ∈ R} a q ≤ M`, and any `c_b ≥ (β' + ω' b)/τ` (`b ≤ M`):
`E_R[(τT − β − ωb)⁺] ≤ τ·ET − β' − ω'·Eb + τ Σ_{b ≤ M} Σ_{j ≤ ⌊c_b⌋} (c_b − j) P(T = j, b)`. -/
theorem sbhLeaf_le {R : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ R, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ)
    {a : ℕ → ℕ} {M : ℕ} (hM : ∑ q ∈ R, a q ≤ M) {τ β β' ω ω' ET Eb : ℝ} (hτ : 0 < τ)
    (hβ : β' ≤ β) (hω' : 0 ≤ ω') (hω : ω' ≤ ω)
    (hET : expect R ν γ (fun w => (tauN R w : ℝ)) ≤ ET)
    (hEb : Eb ≤ expect R ν γ (fun w => (bstat R a w : ℝ)))
    (c : ℕ → ℝ) (hc : ∀ b ≤ M, (β' + ω' * b) / τ ≤ c b) :
    sbhLeaf R ν γ a τ β ω ≤
      τ * ET - β' - ω' * Eb +
        τ * ∑ b ∈ range (M + 1), ∑ j ∈ range (⌊c b⌋₊ + 1), (c b - j) * lawJoint R a ν γ j b := by
  have hanti := sbhLeaf_anti hν γ a τ hβ hω
  rw [sbhLeaf_eq hM ν γ hτ β' ω'] at hanti
  refine hanti.trans ?_
  have hL0 : ∀ j b, 0 ≤ lawJoint R a ν γ j b := fun j b => lawJoint_nonneg hν a γ j b
  have h1 : τ * expect R ν γ (fun w => (tauN R w : ℝ)) ≤ τ * ET :=
    mul_le_mul_of_nonneg_left hET hτ.le
  have h2 : ω' * Eb ≤ ω' * expect R ν γ (fun w => (bstat R a w : ℝ)) :=
    mul_le_mul_of_nonneg_left hEb hω'
  have h3 : ∑ b ∈ range (M + 1), ∑ j ∈ range (⌊(β' + ω' * b) / τ⌋₊ + 1),
        ((β' + ω' * b) / τ - j) * lawJoint R a ν γ j b ≤
      ∑ b ∈ range (M + 1), ∑ j ∈ range (⌊c b⌋₊ + 1), (c b - j) * lawJoint R a ν γ j b :=
    sum_le_sum fun b hb => lowerTail_mono (fun j => lawJoint R a ν γ j b)
      (lawJoint_zero_left R a ν γ b) (fun j => hL0 j b) (hc b (Nat.lt_succ_iff.1 (mem_range.1 hb)))
  have h4 := mul_le_mul_of_nonneg_left h3 hτ.le
  linarith

/-- A row with `c < 1` contributes nothing (`T ≥ 1`); this is `corrSum`'s skip `cW < 2^48`. -/
theorem lowerTail_row_eq_zero (R : Finset ℕ) (a : ℕ → ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) {c : ℝ}
    (hc : c < 1) (b : ℕ) :
    ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * lawJoint R a ν γ j b = 0 := by
  rw [Nat.floor_eq_zero.2 hc]
  simp [lawJoint_zero_left]

end MinModulus.Checker2Math.A
