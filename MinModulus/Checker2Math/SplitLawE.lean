import MinModulus.Checker2Math.Laws

/-!
# `Checker2Math.SplitLawE`: the e-law of the τ-split (semantics of the weighted e-DP)

Owner: L2-B (lean2 stage 2). Namespace `MinModulus.Checker2Math.B`.

Setting: a finite set `L` of numbers (primes, or any numbers `q ≥ 3` with admissible tilts
`0 ≤ ν q ≤ q`: the block phase adds every number left unmarked by the sieve), tilts `ν`, caps `γ`,
and the capped tilted product law of `Smooth` (`Smooth.expect L ν γ`). We write
`e(w) = Σ_{q ∈ L} w q` (`estat`). The e-DP of the checker (`Checker2Impl.ELaw`) processes the
numbers one by one and keeps `w` iff every partial sum of the exponents is `≤ NN` and every
exponent is `≤ acut q`; the partial sums are nondecreasing, so this is `KeptE L NN acut w`
(`e(w) ≤ NN ∧ ∀ q ∈ L, w q ≤ acut q`), independent of the processing order.

The DP stores **weighted** masses `W[e] ≥ 2^e·P(e, kept)` and `lost ≥ E[2^e; ¬kept]`.

## Main results (all exact, for **every** cap `γ`)
* `lawE_empty`, `lostE_empty`: the initial state (`e = 0`).
* `lawE_insert` (**the DP step**, additive convolution): for `q ∉ L`, `e₀ ≤ NN`,
  `P_new(e = e₀, kept) = Σ_{e ≤ NN} Σ_{a ≤ acut q} [e + a = e₀] P_old(e, kept) ρ_q(a)`;
  weighted form `lawE_insert_weighted` (multipliers `2^a ρ_q(a)`), rounded form `lawE_insert_le`.
* `lostE_insert` (**the lost-mass recursion**): for `q ∉ L`,
  `E_new[2^e; lost] = E_old[2^e; lost]·E_q[2^v] + Σ_{e ≤ NN} 2^e P_old(e, kept)·
     (Σ_{a ≤ acut q, e + a > NN} 2^a ρ_q(a) + E_q[2^v 1{v ≥ acut q + 1}])`;
  rounded form `lostE_insert_le`.
* `expect1_two_pow_le`: `E_γ[2^v] ≤ 1 + ν/(q − 2)` (`q ≥ 3`);
  `expect1_two_pow_ge_le`: `E_γ[2^v 1{v ≥ A}] ≤ ν (q − 1) 2^A/(q^A (q − 2))` (`q ≥ 3`, `A ≥ 1`).
* `expect_keptE_eq_sum`: `E[F(e); kept] = Σ_{e ≤ NN} P(e, kept) F(e)`;
  `expect_two_pow_estat_eq`: `E[2^e] = Σ_{e ≤ NN} 2^e P(e, kept) + E[2^e; lost]`.
-/

namespace MinModulus.Checker2Math.B

open Finset MinModulus.Smooth MinModulus.CheckerMath MinModulus.Checker2Math

/-! ### `estat` -/

@[simp] theorem estat_empty (w : ℕ → ℕ) : estat ∅ w = 0 := by simp [estat]

theorem estat_insert {q : ℕ} {L : Finset ℕ} (hq : q ∉ L) (w : ℕ → ℕ) :
    estat (insert q L) w = w q + estat L w := sum_insert hq

theorem estat_update_of_notMem {q : ℕ} {L : Finset ℕ} (hq : q ∉ L) (w : ℕ → ℕ) (a : ℕ) :
    estat L (Function.update w q a) = estat L w := by
  refine sum_congr rfl fun r hr => ?_
  have : r ≠ q := fun h => hq (h ▸ hr)
  rw [Function.update_of_ne this]

theorem estat_insert_update {q : ℕ} {L : Finset ℕ} (hq : q ∉ L) (w : ℕ → ℕ) (a : ℕ) :
    estat (insert q L) (Function.update w q a) = estat L w + a := by
  rw [estat_insert hq, Function.update_self, estat_update_of_notMem hq, add_comm]

/-- `e` is monotone in the configuration. -/
theorem estat_mono (L : Finset ℕ) {v w : ℕ → ℕ} (h : ∀ q ∈ L, v q ≤ w q) :
    estat L v ≤ estat L w :=
  sum_le_sum h

theorem keptE_insert_update {q : ℕ} {L : Finset ℕ} (hq : q ∉ L) (NN : ℕ) (acut : ℕ → ℕ)
    (w : ℕ → ℕ) (a : ℕ) :
    KeptE (insert q L) NN acut (Function.update w q a) ↔
      estat L w + a ≤ NN ∧ a ≤ acut q ∧ ∀ r ∈ L, w r ≤ acut r := by
  unfold KeptE
  rw [estat_insert_update hq, forall_mem_insert, Function.update_self]
  have key : ∀ r ∈ L, (Function.update w q a r ≤ acut r ↔ w r ≤ acut r) := by
    intro r hr
    have : r ≠ q := fun h => hq (h ▸ hr)
    rw [Function.update_of_ne this]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun r hr => (key r hr).1 (h3 r hr)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun r hr => (key r hr).2 (h3 r hr)⟩

/-- Selecting the value of `e` among `e ≤ NN`: for any `X`,
`Σ_{e ≤ NN} [e(w) = e ∧ kept(w)] X(e) = [kept(w)] X(e(w))`. -/
theorem sum_ind_keptE_mul (L : Finset ℕ) (NN : ℕ) (acut : ℕ → ℕ) (w : ℕ → ℕ) (X : ℕ → ℝ) :
    ∑ e ∈ range (NN + 1), (if estat L w = e ∧ KeptE L NN acut w then (1 : ℝ) else 0) * X e =
      if KeptE L NN acut w then X (estat L w) else 0 := by
  have h : ∀ e, (if estat L w = e ∧ KeptE L NN acut w then (1 : ℝ) else 0) * X e =
      if estat L w = e then (if KeptE L NN acut w then X (estat L w) else 0) else 0 := by
    intro e
    by_cases he : estat L w = e
    · subst he
      by_cases hK : KeptE L NN acut w <;> simp [hK]
    · simp [he]
  rw [sum_congr rfl fun e _ => h e, sum_ite_eq]
  by_cases hK : KeptE L NN acut w
  · have : estat L w ∈ range (NN + 1) := mem_range.2 (Nat.lt_succ_of_le hK.1)
    simp [hK, this]
  · simp [hK]

/-! ### Basic properties of `lawE` and `lostE` -/

variable {L : Finset ℕ} {ν : ℕ → ℝ} {γ : ℕ → ℕ} {NN : ℕ} {acut : ℕ → ℕ}

theorem lawE_nonneg (hν : ∀ q ∈ L, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ)
    (e : ℕ) : 0 ≤ lawE L ν γ NN acut e :=
  expect_nonneg hν fun v _ => by split_ifs <;> norm_num

theorem lostE_nonneg (hν : ∀ q ∈ L, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) :
    0 ≤ lostE L ν γ NN acut :=
  expect_nonneg hν fun v _ => by split_ifs <;> positivity

theorem lawE_of_lt (L : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (acut : ℕ → ℕ) {e : ℕ}
    (he : NN < e) : lawE L ν γ NN acut e = 0 := by
  unfold lawE
  refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const L ν γ 0)
  have : ¬ (estat L v = e ∧ KeptE L NN acut v) := by
    rintro ⟨h1, h2, -⟩
    omega
  simp [this]

/-- Initial state of the e-DP: `e = 0` surely. -/
theorem lawE_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) (e : ℕ) :
    lawE ∅ ν γ NN acut e = if e = 0 then 1 else 0 := by
  unfold lawE
  rw [expect_empty]
  have hK : KeptE ∅ NN acut 0 := ⟨by simp, by simp⟩
  by_cases he : e = 0
  · subst he
    simp [hK]
  · rw [ite_eq_right he]
    have : ¬ (estat ∅ (0 : ℕ → ℕ) = e ∧ KeptE ∅ NN acut 0) := by
      rintro ⟨h, -⟩
      simp only [estat_empty] at h
      exact he h.symm
    rw [ite_eq_right this]

theorem lostE_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) :
    lostE ∅ ν γ NN acut = 0 := by
  unfold lostE
  rw [expect_empty]
  have hK : KeptE ∅ NN acut 0 := ⟨by simp, by simp⟩
  simp [hK]

/-! ### `E[F(e); kept] = Σ_e P(e, kept) F(e)` -/

/-- `E[F(e) ; kept] = Σ_{e ≤ NN} P(e, kept) · F(e)`. -/
theorem expect_keptE_eq_sum (L : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ)
    (F : ℕ → ℝ) :
    expect L ν γ (fun w => if KeptE L NN acut w then F (estat L w) else 0) =
      ∑ e ∈ range (NN + 1), lawE L ν γ NN acut e * F e := by
  simp_rw [← sum_ind_keptE_mul L NN acut _ F]
  rw [expect_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [expect_mul_const]
  rfl

/-- **Decomposition** `E[G(w)] = E[G; kept] + E[G; ¬ kept]` with the kept part through the law of
`e`, for `G = F ∘ e`. -/
theorem expect_estat_eq (L : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ)
    (F : ℕ → ℝ) :
    expect L ν γ (fun w => F (estat L w)) =
      ∑ e ∈ range (NN + 1), lawE L ν γ NN acut e * F e +
        expect L ν γ (fun w => if KeptE L NN acut w then 0 else F (estat L w)) := by
  have h : (fun w => F (estat L w)) = fun w =>
      (if KeptE L NN acut w then F (estat L w) else 0) +
      (if KeptE L NN acut w then 0 else F (estat L w)) := by
    funext w
    split_ifs <;> simp
  rw [h, expect_add, expect_keptE_eq_sum]

/-- **Decomposition of `E[2^e]`**: `E[2^e] = Σ_{e ≤ NN} 2^e P(e, kept) + E[2^e; lost]`. -/
theorem expect_two_pow_estat_eq (L : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ)
    (acut : ℕ → ℕ) :
    expect L ν γ (fun w => (2 : ℝ) ^ estat L w) =
      ∑ e ∈ range (NN + 1), (2 : ℝ) ^ e * lawE L ν γ NN acut e + lostE L ν γ NN acut := by
  rw [expect_estat_eq L ν γ NN acut (fun e => (2 : ℝ) ^ e)]
  unfold lostE
  congr 1
  exact sum_congr rfl fun e _ => mul_comm _ _

/-! ### The DP step (additive convolution) -/

/-- Pointwise form of the DP step. -/
theorem ind_keptE_insert_update {q : ℕ} (hq : q ∉ L) (acut : ℕ → ℕ) {e₀ : ℕ} (he₀ : e₀ ≤ NN)
    (w : ℕ → ℕ) (a : ℕ) :
    (if estat (insert q L) (Function.update w q a) = e₀ ∧
        KeptE (insert q L) NN acut (Function.update w q a) then (1 : ℝ) else 0) =
      if a ≤ acut q then
        ∑ e ∈ range (NN + 1), (if estat L w = e ∧ KeptE L NN acut w then (1 : ℝ) else 0) *
          (if e + a = e₀ then 1 else 0)
      else 0 := by
  rw [sum_ind_keptE_mul L NN acut w (fun e => if e + a = e₀ then (1 : ℝ) else 0),
    estat_insert_update hq]
  by_cases hE : ∀ r ∈ L, w r ≤ acut r
  · by_cases ha : a ≤ acut q
    · by_cases he : estat L w + a = e₀
      · have hK : KeptE L NN acut w := ⟨by omega, hE⟩
        have hK' : KeptE (insert q L) NN acut (Function.update w q a) :=
          (keptE_insert_update hq NN acut w a).2 ⟨by omega, ha, hE⟩
        simp [he, hK, hK', ha]
      · simp [he, ha]
    · have hK' : ¬ KeptE (insert q L) NN acut (Function.update w q a) := fun h =>
        ha ((keptE_insert_update hq NN acut w a).1 h).2.1
      simp [hK', ha]
  · have hK' : ¬ KeptE (insert q L) NN acut (Function.update w q a) := fun h =>
      hE ((keptE_insert_update hq NN acut w a).1 h).2.2
    have hK : ¬ KeptE L NN acut w := fun h => hE h.2
    simp [hK', hK]

/-- **The e-DP step** (exact, every cap): for `q ∉ L` and `e₀ ≤ NN`,
`P_{L ∪ {q}}(e = e₀, kept) = Σ_{e ≤ NN} Σ_{a ≤ acut q} [e + a = e₀] P_L(e, kept) ρ_q(a)`. -/
theorem lawE_insert {q : ℕ} (hq : q ∉ L) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ)
    {e₀ : ℕ} (he₀ : e₀ ≤ NN) :
    lawE (insert q L) ν γ NN acut e₀ =
      ∑ e ∈ range (NN + 1), ∑ a ∈ range (acut q + 1),
        if e + a = e₀ then lawE L ν γ NN acut e * rho q (ν q) (γ q) a else 0 := by
  unfold lawE
  rw [expect_insert hq]
  simp_rw [ind_keptE_insert_update hq acut he₀]
  have h2 : ∀ a, expect L ν γ (fun w => if a ≤ acut q then
        ∑ e ∈ range (NN + 1), (if estat L w = e ∧ KeptE L NN acut w then (1 : ℝ) else 0) *
          (if e + a = e₀ then 1 else 0) else 0) =
      if a ≤ acut q then ∑ e ∈ range (NN + 1),
        expect L ν γ (fun w => if estat L w = e ∧ KeptE L NN acut w then 1 else 0) *
          (if e + a = e₀ then 1 else 0) else 0 := by
    intro a
    split_ifs
    · rw [expect_sum]
      exact sum_congr rfl fun e _ => expect_mul_const _ _
    · exact expect_const L ν γ 0
  simp_rw [h2]
  rw [sum_rho_ite_eq]
  simp_rw [mul_sum]
  refine sum_comm.trans (sum_congr rfl fun e _ => sum_congr rfl fun a _ => ?_)
  split_ifs <;> ring

/-- **The weighted e-DP step** (exact): multipliers `2^a ρ_q(a)` on weighted masses
`2^e P(e, kept)`. -/
theorem lawE_insert_weighted {q : ℕ} (hq : q ∉ L) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ)
    (acut : ℕ → ℕ) {e₀ : ℕ} (he₀ : e₀ ≤ NN) :
    (2 : ℝ) ^ e₀ * lawE (insert q L) ν γ NN acut e₀ =
      ∑ e ∈ range (NN + 1), ∑ a ∈ range (acut q + 1),
        if e + a = e₀ then ((2 : ℝ) ^ e * lawE L ν γ NN acut e) *
          ((2 : ℝ) ^ a * rho q (ν q) (γ q) a) else 0 := by
  rw [lawE_insert hq ν γ NN acut he₀, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [← h, pow_add]
    ring
  · ring

/-- **The weighted e-DP step with upper bounds**: `D e ≥ 2^e P_old(e, kept)` on `[0, NN]` and
`ℓ a ≥ 2^a ρ_q(a)` on `[0, acut q]` give
`Σ_{e,a} [e + a = e₀] D e ℓ a ≥ 2^{e₀} P_new(e₀, kept)`. -/
theorem lawE_insert_le {q : ℕ} (hq : q ∉ L) (hν : ∀ r ∈ insert q L, 0 ≤ ν r ∧ ν r ≤ r)
    (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) (D ℓ : ℕ → ℝ)
    (hD : ∀ e ≤ NN, (2 : ℝ) ^ e * lawE L ν γ NN acut e ≤ D e)
    (hℓ : ∀ a ≤ acut q, (2 : ℝ) ^ a * rho q (ν q) (γ q) a ≤ ℓ a) {e₀ : ℕ} (he₀ : e₀ ≤ NN) :
    (2 : ℝ) ^ e₀ * lawE (insert q L) ν γ NN acut e₀ ≤
      ∑ e ∈ range (NN + 1), ∑ a ∈ range (acut q + 1),
        if e + a = e₀ then D e * ℓ a else 0 := by
  rw [lawE_insert_weighted hq ν γ NN acut he₀]
  have hν' : ∀ r ∈ L, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
  have hνq := hν q (mem_insert_self q L)
  refine sum_le_sum fun e he => sum_le_sum fun a ha => ?_
  split_ifs
  · have he' := Nat.lt_succ_iff.1 (mem_range.1 he)
    have ha' := Nat.lt_succ_iff.1 (mem_range.1 ha)
    have h0 : 0 ≤ (2 : ℝ) ^ e * lawE L ν γ NN acut e :=
      mul_nonneg (by positivity) (lawE_nonneg hν' γ NN acut e)
    have h1 : 0 ≤ (2 : ℝ) ^ a * rho q (ν q) (γ q) a :=
      mul_nonneg (by positivity) (rho_nonneg hνq.1 hνq.2 _ _)
    exact mul_le_mul (hD e he') (hℓ a ha') h1 (h0.trans (hD e he'))
  · exact le_rfl

/-! ### The lost-mass recursion -/

/-- The factor of a kept path with partial sum `e` at the new number: the path is lost at this
step iff `e + a > NN` or `a > acut q`; it then contributes `2^a`. -/
noncomputable def lostIndE (NN ac e a : ℕ) : ℝ := if NN < e + a ∨ ac < a then (2 : ℝ) ^ a else 0

/-- Pointwise form of the lost-mass recursion. -/
theorem lostE_insert_update {q : ℕ} (hq : q ∉ L) (NN : ℕ) (acut : ℕ → ℕ) (w : ℕ → ℕ) (a : ℕ) :
    (if KeptE (insert q L) NN acut (Function.update w q a) then (0 : ℝ)
      else (2 : ℝ) ^ estat (insert q L) (Function.update w q a)) =
      (2 : ℝ) ^ a * (if KeptE L NN acut w then 0 else (2 : ℝ) ^ estat L w) +
      ∑ e ∈ range (NN + 1), (if estat L w = e ∧ KeptE L NN acut w then (1 : ℝ) else 0) *
        ((2 : ℝ) ^ e * lostIndE NN (acut q) e a) := by
  rw [sum_ind_keptE_mul L NN acut w (fun e => (2 : ℝ) ^ e * lostIndE NN (acut q) e a),
    estat_insert_update hq, pow_add]
  by_cases hK : KeptE L NN acut w
  · by_cases hl : NN < estat L w + a ∨ acut q < a
    · have hK' : ¬ KeptE (insert q L) NN acut (Function.update w q a) := by
        intro h
        rw [keptE_insert_update hq] at h
        omega
      simp [hK, hK', lostIndE, hl]
    · have hK' : KeptE (insert q L) NN acut (Function.update w q a) := by
        rw [keptE_insert_update hq]
        exact ⟨by omega, by omega, hK.2⟩
      simp [hK, hK', lostIndE, hl]
  · have hK' : ¬ KeptE (insert q L) NN acut (Function.update w q a) := by
      intro h
      rw [keptE_insert_update hq] at h
      apply hK
      exact ⟨by omega, h.2.2⟩
    simp [hK, hK']
    ring

/-- The one-coordinate factor of the lost-mass recursion, split into the kept exponents
`a ≤ acut q` with `e + a > NN` and the truncated exponents `a ≥ acut q + 1`. -/
theorem expect1_lostIndE (q : ℕ) (νq : ℝ) (γq NN ac e : ℕ) :
    expect1 q νq γq (fun a => lostIndE NN ac e a) =
      ∑ a ∈ range (ac + 1), (if NN < e + a then (2 : ℝ) ^ a * rho q νq γq a else 0) +
        expect1 q νq γq (fun a => if ac + 1 ≤ a then (2 : ℝ) ^ a else 0) := by
  have hsplit : (fun a => lostIndE NN ac e a) = fun a =>
      (if a ≤ ac then (if NN < e + a then (2 : ℝ) ^ a else 0) else 0) +
        (if ac + 1 ≤ a then (2 : ℝ) ^ a else 0) := by
    funext a
    unfold lostIndE
    by_cases ha : a ≤ ac
    · have h1 : ¬ ac + 1 ≤ a := by omega
      have h2 : ¬ ac < a := by omega
      simp [ha, h1, h2]
    · have h1 : ac + 1 ≤ a := by omega
      have h2 : ac < a := by omega
      simp [ha, h1, h2]
  rw [hsplit, expect1_add]
  congr 1
  unfold expect1
  rw [sum_rho_ite_eq]
  refine sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

/-- **The lost-mass recursion of the e-DP** (exact, every cap): for `q ∉ L`,
`E_new[2^e; lost] = E_old[2^e; lost] · E_q[2^v] + Σ_{e ≤ NN} 2^e P_old(e, kept) ·
  (Σ_{a ≤ acut q, NN < e + a} 2^a ρ_q(a) + E_q[2^v 1{v ≥ acut q + 1}])`. -/
theorem lostE_insert {q : ℕ} (hq : q ∉ L) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) :
    lostE (insert q L) ν γ NN acut =
      lostE L ν γ NN acut * expect1 q (ν q) (γ q) (fun a => (2 : ℝ) ^ a) +
      ∑ e ∈ range (NN + 1), (2 : ℝ) ^ e * lawE L ν γ NN acut e *
        (∑ a ∈ range (acut q + 1), (if NN < e + a then (2 : ℝ) ^ a * rho q (ν q) (γ q) a else 0) +
          expect1 q (ν q) (γ q) (fun a => if acut q + 1 ≤ a then (2 : ℝ) ^ a else 0)) := by
  have e1 : ∀ e ∈ range (NN + 1),
      (2 : ℝ) ^ e * lawE L ν γ NN acut e *
        (∑ a ∈ range (acut q + 1),
            (if NN < e + a then (2 : ℝ) ^ a * rho q (ν q) (γ q) a else 0) +
          expect1 q (ν q) (γ q) (fun a => if acut q + 1 ≤ a then (2 : ℝ) ^ a else 0)) =
      (2 : ℝ) ^ e * lawE L ν γ NN acut e *
        expect1 q (ν q) (γ q) (fun a => lostIndE NN (acut q) e a) := by
    intro e _
    rw [expect1_lostIndE]
  rw [sum_congr rfl e1, lostE, expect_insert hq]
  simp_rw [lostE_insert_update hq NN acut]
  have h2 : ∀ a : ℕ, expect L ν γ (fun w => (2 : ℝ) ^ a *
        (if KeptE L NN acut w then 0 else (2 : ℝ) ^ estat L w) +
        ∑ e ∈ range (NN + 1), (if estat L w = e ∧ KeptE L NN acut w then (1 : ℝ) else 0) *
          ((2 : ℝ) ^ e * lostIndE NN (acut q) e a)) =
      (2 : ℝ) ^ a * lostE L ν γ NN acut + ∑ e ∈ range (NN + 1),
        lawE L ν γ NN acut e * ((2 : ℝ) ^ e * lostIndE NN (acut q) e a) := by
    intro a
    rw [expect_add, expect_const_mul, expect_sum]
    congr 1
    exact sum_congr rfl fun e _ => expect_mul_const _ _
  simp_rw [h2]
  simp only [mul_add, sum_add_distrib]
  congr 1
  · unfold expect1
    rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  · unfold expect1
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun e _ => sum_congr rfl fun a _ => by ring

/-- The lost-mass recursion with upper bounds: `Lb ≥ E_old[2^e; lost]`,
`D e ≥ 2^e P_old(e, kept)` on `[0, NN]`, `E2 ≥ E_q[2^v]`, `ℓ a ≥ 2^a ρ_q(a)` on `[0, acut q]`,
`H ≥ E_q[2^v 1{v ≥ acut q + 1}]` give
`Lb · E2 + Σ_{e ≤ NN} D e · (Σ_{a ≤ acut q, NN < e + a} ℓ a + H) ≥ E_new[2^e; lost]`. -/
theorem lostE_insert_le {q : ℕ} (hq : q ∉ L) (hν : ∀ r ∈ insert q L, 0 ≤ ν r ∧ ν r ≤ r)
    (γ : ℕ → ℕ) (NN : ℕ) (acut : ℕ → ℕ) (Lb E2 H : ℝ) (D ℓ : ℕ → ℝ)
    (hL : lostE L ν γ NN acut ≤ Lb)
    (hD : ∀ e ≤ NN, (2 : ℝ) ^ e * lawE L ν γ NN acut e ≤ D e)
    (hE2 : expect1 q (ν q) (γ q) (fun a => (2 : ℝ) ^ a) ≤ E2)
    (hℓ : ∀ a ≤ acut q, (2 : ℝ) ^ a * rho q (ν q) (γ q) a ≤ ℓ a)
    (hH : expect1 q (ν q) (γ q) (fun a => if acut q + 1 ≤ a then (2 : ℝ) ^ a else 0) ≤ H) :
    lostE (insert q L) ν γ NN acut ≤
      Lb * E2 + ∑ e ∈ range (NN + 1), D e *
        (∑ a ∈ range (acut q + 1), (if NN < e + a then ℓ a else 0) + H) := by
  rw [lostE_insert hq ν γ NN acut]
  have hν' : ∀ r ∈ L, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
  have hνq := hν q (mem_insert_self q L)
  have hE0 : 0 ≤ expect1 q (ν q) (γ q) (fun a => (2 : ℝ) ^ a) :=
    expect1_nonneg hνq.1 hνq.2 fun a _ => by positivity
  have hH0 : 0 ≤ expect1 q (ν q) (γ q) (fun a => if acut q + 1 ≤ a then (2 : ℝ) ^ a else 0) :=
    expect1_nonneg hνq.1 hνq.2 fun a _ => by split_ifs <;> positivity
  refine add_le_add ?_ (sum_le_sum fun e he => ?_)
  · exact mul_le_mul hL hE2 hE0 ((lostE_nonneg hν' γ NN acut).trans hL)
  · have he' := Nat.lt_succ_iff.1 (mem_range.1 he)
    have h0 : 0 ≤ (2 : ℝ) ^ e * lawE L ν γ NN acut e :=
      mul_nonneg (by positivity) (lawE_nonneg hν' γ NN acut e)
    have hin0 : 0 ≤ ∑ a ∈ range (acut q + 1),
        (if NN < e + a then (2 : ℝ) ^ a * rho q (ν q) (γ q) a else 0) :=
      sum_nonneg fun a _ => by
        split_ifs
        · exact mul_nonneg (by positivity) (rho_nonneg hνq.1 hνq.2 _ _)
        · exact le_rfl
    have hin : ∑ a ∈ range (acut q + 1),
        (if NN < e + a then (2 : ℝ) ^ a * rho q (ν q) (γ q) a else 0) ≤
        ∑ a ∈ range (acut q + 1), (if NN < e + a then ℓ a else 0) :=
      sum_le_sum fun a ha => by
        split_ifs
        · exact hℓ a (Nat.lt_succ_iff.1 (mem_range.1 ha))
        · exact le_rfl
    exact mul_le_mul (hD e he') (add_le_add hin hH) (add_nonneg hin0 hH0) (h0.trans (hD e he'))

/-! ### One-coordinate bounds, uniform in the cap -/

/-- `Σ_{r < n} x^{r+1} 2^r ≤ x/(1 − 2x)` for `0 ≤ x`, `2x < 1`. -/
theorem sum_range_pow_succ_two_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : 2 * x < 1) (n : ℕ) :
    ∑ r ∈ range n, x ^ (r + 1) * (2 : ℝ) ^ r ≤ x / (1 - 2 * x) := by
  have h := sum_range_pow_succ_le (x := 2 * x) (by positivity) hx1 n
  have e : ∑ r ∈ range n, x ^ (r + 1) * (2 : ℝ) ^ r = (1 / 2) * ∑ r ∈ range n, (2 * x) ^ (r + 1) := by
    rw [mul_sum]
    refine sum_congr rfl fun r _ => ?_
    rw [mul_pow, pow_succ 2 r]
    ring
  rw [e]
  have e2 : (1 / 2 : ℝ) * ((2 * x) / (1 - 2 * x)) = x / (1 - 2 * x) := by ring
  rw [← e2]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- **`E_γ[2^v] ≤ 1 + ν/(q − 2)`** for `q ≥ 3`, every cap `γ` (`= 1 + Σ_{j=1}^{γ} ν q^{-j} 2^{j-1}`). -/
theorem expect1_two_pow_le {q : ℕ} (hq : 3 ≤ q) {ν : ℝ} (hν : 0 ≤ ν) (γ : ℕ) :
    expect1 q ν γ (fun a => (2 : ℝ) ^ a) ≤ 1 + ν / ((q : ℝ) - 2) := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hx0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have hx1 : 2 * (q : ℝ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by linarith)]
    linarith
  rw [expect1_eq_geom]
  have e : ∑ r ∈ range γ, ((q : ℝ)⁻¹) ^ (r + 1) * ((2 : ℝ) ^ (r + 1) - (2 : ℝ) ^ r) =
      ∑ r ∈ range γ, ((q : ℝ)⁻¹) ^ (r + 1) * (2 : ℝ) ^ r := by
    refine sum_congr rfl fun r _ => ?_
    rw [pow_succ]
    ring
  rw [e, pow_zero]
  have h := mul_le_mul_of_nonneg_left (sum_range_pow_succ_two_pow_le hx0 hx1 γ) hν
  have e2 : (q : ℝ)⁻¹ / (1 - 2 * (q : ℝ)⁻¹) = 1 / ((q : ℝ) - 2) := by
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have hq2 : (q : ℝ) - 2 ≠ 0 := by linarith
    field_simp
  rw [e2] at h
  have : ν * (1 / ((q : ℝ) - 2)) = ν / ((q : ℝ) - 2) := by ring
  linarith

/-- Exact partial tail for `E[2^v 1{v ≥ A}]`: for `A ≥ 1`,
`Σ_{r<γ} x^{r+1}(g(r+1) − g(r)) = [A ≤ γ] (x^A 2^A + Σ_{j ∈ [A, γ)} x^{j+1} 2^j)`
where `g(a) = 2^a 1{a ≥ A}`. -/
theorem h2Tail_eq {x : ℝ} {A : ℕ} (hA : 1 ≤ A) (γ : ℕ) :
    ∑ r ∈ range γ, x ^ (r + 1) * ((if A ≤ r + 1 then (2 : ℝ) ^ (r + 1) else 0) -
        (if A ≤ r then (2 : ℝ) ^ r else 0)) =
      if γ < A then 0 else x ^ A * (2 : ℝ) ^ A + ∑ j ∈ Ico A γ, x ^ (j + 1) * (2 : ℝ) ^ j := by
  induction γ with
  | zero =>
    rw [ite_eq_left (by omega)]
    simp
  | succ γ ih =>
    rw [sum_range_succ, ih]
    rcases lt_trichotomy (γ + 1) A with h | h | h
    · rw [ite_eq_left (by omega), ite_eq_left h, ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
      subst h
      simp
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
        ite_eq_right (by omega), sum_Ico_succ_top (by omega : A ≤ γ)]
      rw [pow_succ (2 : ℝ) γ]
      ring

/-- **`E_γ[2^v 1{v ≥ A}] ≤ ν (q − 1) 2^A / (q^A (q − 2))`** for `q ≥ 3`, `A ≥ 1`, every cap `γ`. -/
theorem expect1_two_pow_ge_le {q : ℕ} (hq : 3 ≤ q) {ν : ℝ} (hν : 0 ≤ ν) {A : ℕ} (hA : 1 ≤ A)
    (γ : ℕ) :
    expect1 q ν γ (fun a => if A ≤ a then (2 : ℝ) ^ a else 0) ≤
      ν * ((q : ℝ) - 1) * 2 ^ A / ((q : ℝ) ^ A * ((q : ℝ) - 2)) := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set x := (q : ℝ)⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : 2 * x < 1 := by
    rw [hx, ← div_eq_mul_inv, div_lt_one hq0]
    linarith
  rw [expect1_eq_geom]
  have hg0 : (if A ≤ 0 then (2 : ℝ) ^ 0 else 0) = 0 := ite_eq_right (by omega)
  simp only [hg0, zero_add]
  rw [h2Tail_eq hA γ]
  -- the bound on the geometric tail
  have hgeo := geom_sum_Ico_le_of_lt_one (m := A) (n := γ) (by positivity : 0 ≤ 2 * x) hx1
  have e1 : ∑ j ∈ Ico A γ, x ^ (j + 1) * (2 : ℝ) ^ j = x * ∑ j ∈ Ico A γ, (2 * x) ^ j := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_pow, pow_succ]
    ring
  have hxA : 0 ≤ x ^ A * (2 : ℝ) ^ A := by positivity
  -- the closed form of the bound
  have hclosed : x ^ A * (2 : ℝ) ^ A + x * ((2 * x) ^ A / (1 - 2 * x)) =
      ((q : ℝ) - 1) * 2 ^ A / ((q : ℝ) ^ A * ((q : ℝ) - 2)) := by
    have hq2 : (q : ℝ) - 2 ≠ 0 := by linarith
    have hqA : (q : ℝ) ^ A ≠ 0 := by positivity
    rw [hx, mul_pow, inv_pow]
    field_simp
    ring
  have hRHS : 0 ≤ ((q : ℝ) - 1) * 2 ^ A / ((q : ℝ) ^ A * ((q : ℝ) - 2)) := by
    have : 0 ≤ (q : ℝ) - 1 := by linarith
    have : 0 < (q : ℝ) - 2 := by linarith
    positivity
  split_ifs
  · rw [mul_zero]
    have : 0 ≤ ν * ((q : ℝ) - 1) * 2 ^ A / ((q : ℝ) ^ A * ((q : ℝ) - 2)) := by
      rw [mul_assoc, mul_div_assoc]
      exact mul_nonneg hν hRHS
    exact this
  · rw [e1]
    have h1 : x ^ A * (2 : ℝ) ^ A + x * ∑ j ∈ Ico A γ, (2 * x) ^ j ≤
        ((q : ℝ) - 1) * 2 ^ A / ((q : ℝ) ^ A * ((q : ℝ) - 2)) := by
      rw [← hclosed]
      have := mul_le_mul_of_nonneg_left hgeo hx0
      linarith
    have := mul_le_mul_of_nonneg_left h1 hν
    rw [mul_assoc, mul_div_assoc]
    exact this

end MinModulus.Checker2Math.B
