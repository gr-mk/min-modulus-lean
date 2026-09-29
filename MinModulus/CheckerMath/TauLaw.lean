import MinModulus.Smooth.Main

/-!
# `CheckerMath`, part 1: the law of `τ` under truncation (semantics of the τ-DP)

Setting: a finite set `Ps` of primes, tilts `ν`, caps `γ`, and the capped tilted product law of
`Smooth` (`Smooth.expect Ps ν γ`). We write `τ(v) = ∏_{q ∈ Ps} (v q + 1)` (`tauN`); for primes
it is the number of divisors of `s(v) = Smooth.smooth Ps v` (`card_divisors_smooth_eq_tauN`).

A truncated DP (`rigcert.c`'s `dp_step`, or the Lean checker's `dpStep`) processes the primes one
by one and keeps a configuration `v` iff every partial product of the factors `v q + 1` is
`≤ TM` and every exponent is `≤ acut q`. The partial products are nondecreasing, so this is
`τ(v) ≤ TM ∧ ∀ q ∈ Ps, v q ≤ acut q` (`Kept`), which does not depend on the processing order.

## Definitions
* `lawKept Ps ν γ TM acut T = P(τ = T ∧ kept)`;
* `lostMass Ps ν γ TM acut = E[τ ; ¬ kept]`;
* `expLostProb Ps ν γ acut = P(∃ q ∈ Ps, v q > acut q)`.

## Main results (all exact, for **every** cap `γ`)
* `lawKept_empty`, `lostMass_empty`: the initial state (`τ = 1`).
* `lawKept_insert` (**the DP step**, multiplicative convolution): for `q ∉ Ps`, `T ≤ TM`,
  `P_new(τ = T, kept) = Σ_{t ≤ TM} Σ_{a ≤ acut q} [t (a+1) = T] P_old(τ = t, kept) ρ_q(a)`.
  Rounded versions: `lawKept_insert_le` (upper bounds `D ≥ P_old`, `ℓ ≥ ρ`) and
  `le_lawKept_insert` (lower bounds).
* `lostMass_insert` (**the lost-mass recursion**): for `q ∉ Ps`,
  `E_new[τ; lost] = E_old[τ; lost] · E[v_q+1] + Σ_{t ≤ TM} P_old(τ = t, kept) · t · h_γ(A_t)`,
  `A_t = min(⌊TM/t⌋, acut q + 1)`, `h_γ(A) = E[(v_q+1) 1{v_q ≥ A}]`.
  Rounded version `lostMass_insert_le`.
* `expect1_add_one_le`: `E_γ[v+1] ≤ 1 + ν/(q-1)`; `expect1_hA_le`:
  `h_γ(A) ≤ ν q^{-A} (A + 1 + 1/(q-1))` for `A ≥ 1` (every cap `γ`).
* `expect_kept_eq_sum`: `E[F(τ); kept] = Σ_{T ≤ TM} P(τ = T, kept) F(T)`;
  `expect_tauN_eq`: `E[τ] = Σ_{T ≤ TM} T · P(τ = T, kept) + E[τ; lost]`;
  `expect_tauN_le`: `E[τ] ≤ ∏_{q ∈ Ps} (1 + ν_q/(q-1))`.
* `expLostProb_le`: `P(∃ q, v q > acut q) ≤ Σ_q ν_q q^{-(acut q + 1)}` (union bound).

## Caps
Every identity above holds for every cap `γ`. The DP arrays of the checker are computed with the
*untruncated* point masses `P(V = a) = ν q^{-a}(1 - 1/q)` (`a ≥ 1`), `1 - ν/q` (`a = 0`); these
equal `ρ(q, ν, γ, a)` whenever `a < γ q` (`Smooth.rho_zero_of_pos`, `Smooth.rho_of_pos_of_lt`),
so the hypothesis `ρ ≤ ℓ` of `lawKept_insert_le` holds as soon as `acut q < γ q`. Small caps are
handled once, at the top level, by monotone coupling (see `ComparisonBound.lean`).
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth

/-! ### `τ` as a natural number -/

/-- `τ(v) = ∏_{q ∈ Ps} (v q + 1)`, as a natural number (`= (smooth Ps v).divisors.card` when
`Ps` consists of primes). -/
def tauN (Ps : Finset ℕ) (v : ℕ → ℕ) : ℕ := ∏ q ∈ Ps, (v q + 1)

theorem tauN_pos (Ps : Finset ℕ) (v : ℕ → ℕ) : 0 < tauN Ps v :=
  prod_pos fun q _ => Nat.succ_pos (v q)

theorem one_le_tauN (Ps : Finset ℕ) (v : ℕ → ℕ) : 1 ≤ tauN Ps v := tauN_pos Ps v

theorem one_le_tauN_real (Ps : Finset ℕ) (v : ℕ → ℕ) : (1 : ℝ) ≤ tauN Ps v := by
  exact_mod_cast one_le_tauN Ps v

theorem tauN_real_nonneg (Ps : Finset ℕ) (v : ℕ → ℕ) : (0 : ℝ) ≤ tauN Ps v := by positivity

@[simp] theorem tauN_empty (v : ℕ → ℕ) : tauN ∅ v = 1 := by simp [tauN]

theorem tauN_insert {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) (v : ℕ → ℕ) :
    tauN (insert q Ps) v = (v q + 1) * tauN Ps v := prod_insert hq

theorem tauN_update_of_notMem {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) (v : ℕ → ℕ) (a : ℕ) :
    tauN Ps (Function.update v q a) = tauN Ps v := by
  refine prod_congr rfl fun r hr => ?_
  have : r ≠ q := fun h => hq (h ▸ hr)
  rw [Function.update_of_ne this]

theorem tauN_insert_update {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) (v : ℕ → ℕ) (a : ℕ) :
    tauN (insert q Ps) (Function.update v q a) = tauN Ps v * (a + 1) := by
  rw [tauN_insert hq, Function.update_self, tauN_update_of_notMem hq, mul_comm]

/-- For primes, `τ(s(v)) = tauN Ps v`. -/
theorem card_divisors_smooth_eq_tauN {Ps : Finset ℕ} (hPs : ∀ q ∈ Ps, q.Prime) (v : ℕ → ℕ) :
    (smooth Ps v).divisors.card = tauN Ps v :=
  card_divisors_smooth hPs v

theorem tauN_cast (Ps : Finset ℕ) (v : ℕ → ℕ) :
    (tauN Ps v : ℝ) = ∏ q ∈ Ps, ((v q : ℝ) + 1) := by
  unfold tauN
  push_cast
  rfl

/-- `τ` is monotone in the configuration. -/
theorem tauN_mono (Ps : Finset ℕ) {v w : ℕ → ℕ} (h : ∀ q ∈ Ps, v q ≤ w q) :
    tauN Ps v ≤ tauN Ps w :=
  prod_le_prod fun q hq => Nat.succ_le_succ (h q hq)

/-! ### Kept configurations -/

/-- The truncated DP keeps `v` iff `τ(v) ≤ TM` and `v q ≤ acut q` for every `q ∈ Ps`. -/
def Kept (Ps : Finset ℕ) (TM : ℕ) (acut : ℕ → ℕ) (v : ℕ → ℕ) : Prop :=
  tauN Ps v ≤ TM ∧ ∀ q ∈ Ps, v q ≤ acut q

instance (Ps : Finset ℕ) (TM : ℕ) (acut : ℕ → ℕ) : DecidablePred (Kept Ps TM acut) :=
  fun v => inferInstanceAs (Decidable (tauN Ps v ≤ TM ∧ ∀ q ∈ Ps, v q ≤ acut q))

theorem kept_insert_update {q : ℕ} {Ps : Finset ℕ} (hq : q ∉ Ps) (TM : ℕ) (acut : ℕ → ℕ)
    (w : ℕ → ℕ) (a : ℕ) :
    Kept (insert q Ps) TM acut (Function.update w q a) ↔
      tauN Ps w * (a + 1) ≤ TM ∧ a ≤ acut q ∧ ∀ r ∈ Ps, w r ≤ acut r := by
  unfold Kept
  rw [tauN_insert_update hq, forall_mem_insert, Function.update_self]
  have key : ∀ r ∈ Ps, (Function.update w q a r ≤ acut r ↔ w r ≤ acut r) := by
    intro r hr
    have : r ≠ q := fun h => hq (h ▸ hr)
    rw [Function.update_of_ne this]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun r hr => (key r hr).1 (h3 r hr)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun r hr => (key r hr).2 (h3 r hr)⟩

/-- Selecting the value of `τ` among `T ≤ TM`: for any `X`,
`Σ_{T ≤ TM} [τ(v) = T ∧ kept(v)] X(T) = [kept(v)] X(τ(v))`. -/
theorem sum_ind_kept_mul (Ps : Finset ℕ) (TM : ℕ) (acut : ℕ → ℕ) (v : ℕ → ℕ) (X : ℕ → ℝ) :
    ∑ T ∈ range (TM + 1), (if tauN Ps v = T ∧ Kept Ps TM acut v then (1 : ℝ) else 0) * X T =
      if Kept Ps TM acut v then X (tauN Ps v) else 0 := by
  have h : ∀ T, (if tauN Ps v = T ∧ Kept Ps TM acut v then (1 : ℝ) else 0) * X T =
      if tauN Ps v = T then (if Kept Ps TM acut v then X (tauN Ps v) else 0) else 0 := by
    intro T
    by_cases hT : tauN Ps v = T
    · subst hT
      by_cases hK : Kept Ps TM acut v <;> simp [hK]
    · simp [hT]
  rw [sum_congr rfl fun T _ => h T, sum_ite_eq]
  by_cases hK : Kept Ps TM acut v
  · have : tauN Ps v ∈ range (TM + 1) := mem_range.2 (Nat.lt_succ_of_le hK.1)
    simp [hK, this]
  · simp [hK]

/-! ### The truncated law and the lost mass -/

/-- `P(τ = T ∧ kept)` under the capped tilted law. -/
noncomputable def lawKept (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ)
    (T : ℕ) : ℝ :=
  expect Ps ν γ (fun v => if tauN Ps v = T ∧ Kept Ps TM acut v then 1 else 0)

/-- `E[τ ; ¬ kept]`: the `τ`-mass lost by the truncated DP. -/
noncomputable def lostMass (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ) :
    ℝ :=
  expect Ps ν γ (fun v => if Kept Ps TM acut v then 0 else (tauN Ps v : ℝ))

/-- `P(∃ q ∈ Ps, v q > acut q)`: the probability that some exponent is truncated. -/
noncomputable def expLostProb (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (acut : ℕ → ℕ) : ℝ :=
  expect Ps ν γ (fun v => if ∃ q ∈ Ps, acut q < v q then 1 else 0)

variable {Ps : Finset ℕ} {ν : ℕ → ℝ} {γ : ℕ → ℕ} {TM : ℕ} {acut : ℕ → ℕ}

theorem lawKept_nonneg (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ)
    (T : ℕ) : 0 ≤ lawKept Ps ν γ TM acut T :=
  expect_nonneg hν fun v _ => by split_ifs <;> norm_num

theorem lostMass_nonneg (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (TM : ℕ)
    (acut : ℕ → ℕ) : 0 ≤ lostMass Ps ν γ TM acut :=
  expect_nonneg hν fun v _ => by split_ifs <;> positivity

theorem expLostProb_nonneg (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (acut : ℕ → ℕ) :
    0 ≤ expLostProb Ps ν γ acut :=
  expect_nonneg hν fun v _ => by split_ifs <;> norm_num

theorem lawKept_of_lt (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (acut : ℕ → ℕ) {T : ℕ}
    (hT : TM < T) : lawKept Ps ν γ TM acut T = 0 := by
  unfold lawKept
  refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const Ps ν γ 0)
  have : ¬ (tauN Ps v = T ∧ Kept Ps TM acut v) := by
    rintro ⟨h1, h2, -⟩
    omega
  simp [this]

theorem lawKept_zero (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ) :
    lawKept Ps ν γ TM acut 0 = 0 := by
  unfold lawKept
  refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const Ps ν γ 0)
  have : ¬ (tauN Ps v = 0 ∧ Kept Ps TM acut v) := by
    rintro ⟨h1, -⟩
    exact (tauN_pos Ps v).ne' h1
  simp [this]

/-- Initial state of the DP: `τ = 1` surely. -/
theorem lawKept_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (hTM : 1 ≤ TM) (acut : ℕ → ℕ) (T : ℕ) :
    lawKept ∅ ν γ TM acut T = if T = 1 then 1 else 0 := by
  unfold lawKept
  rw [expect_empty]
  have hK : Kept ∅ TM acut 0 := ⟨by simpa using hTM, by simp⟩
  by_cases hT : T = 1
  · subst hT
    simp [hK]
  · rw [ite_eq_right hT]
    have : ¬ (tauN ∅ (0 : ℕ → ℕ) = T ∧ Kept ∅ TM acut 0) := by
      rintro ⟨h, -⟩
      simp only [tauN_empty] at h
      exact hT h.symm
    rw [ite_eq_right this]

theorem lostMass_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (hTM : 1 ≤ TM) (acut : ℕ → ℕ) :
    lostMass ∅ ν γ TM acut = 0 := by
  unfold lostMass
  rw [expect_empty]
  have hK : Kept ∅ TM acut 0 := ⟨by simpa using hTM, by simp⟩
  simp [hK]

theorem expLostProb_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (acut : ℕ → ℕ) :
    expLostProb ∅ ν γ acut = 0 := by
  simp [expLostProb]

/-! ### `E[F(τ); kept] = Σ_T P(τ = T, kept) F(T)` and the decomposition of `E[τ]` -/

/-- `E[F(τ) ; kept] = Σ_{T ≤ TM} P(τ = T, kept) · F(T)`. -/
theorem expect_kept_eq_sum (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ)
    (F : ℕ → ℝ) :
    expect Ps ν γ (fun v => if Kept Ps TM acut v then F (tauN Ps v) else 0) =
      ∑ T ∈ range (TM + 1), lawKept Ps ν γ TM acut T * F T := by
  simp_rw [← sum_ind_kept_mul Ps TM acut _ F]
  rw [expect_sum]
  refine sum_congr rfl fun T _ => ?_
  rw [expect_mul_const]
  rfl

/-- **Decomposition of the first moment**:
`E[τ] = Σ_{T ≤ TM} T · P(τ = T, kept) + E[τ; lost]`. -/
theorem expect_tauN_eq (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ) :
    expect Ps ν γ (fun v => (tauN Ps v : ℝ)) =
      ∑ T ∈ range (TM + 1), (T : ℝ) * lawKept Ps ν γ TM acut T + lostMass Ps ν γ TM acut := by
  have h : (fun v => (tauN Ps v : ℝ)) = fun v =>
      (if Kept Ps TM acut v then (tauN Ps v : ℝ) else 0) +
      (if Kept Ps TM acut v then 0 else (tauN Ps v : ℝ)) := by
    funext v
    split_ifs <;> simp
  rw [h, expect_add, expect_kept_eq_sum Ps ν γ TM acut (fun T => (T : ℝ))]
  unfold lostMass
  congr 1
  exact sum_congr rfl fun T _ => mul_comm _ _

/-! ### The DP step (multiplicative convolution) -/

/-- Pointwise form of the DP step. -/
theorem ind_kept_insert_update {q : ℕ} (hq : q ∉ Ps) (acut : ℕ → ℕ) {T : ℕ} (hT : T ≤ TM)
    (w : ℕ → ℕ) (a : ℕ) :
    (if tauN (insert q Ps) (Function.update w q a) = T ∧
        Kept (insert q Ps) TM acut (Function.update w q a) then (1 : ℝ) else 0) =
      if a ≤ acut q then
        ∑ t ∈ range (TM + 1), (if tauN Ps w = t ∧ Kept Ps TM acut w then (1 : ℝ) else 0) *
          (if t * (a + 1) = T then 1 else 0)
      else 0 := by
  rw [sum_ind_kept_mul Ps TM acut w (fun t => if t * (a + 1) = T then (1 : ℝ) else 0),
    tauN_insert_update hq]
  have h1 : tauN Ps w ≤ tauN Ps w * (a + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos a)
  by_cases hE : ∀ r ∈ Ps, w r ≤ acut r
  · by_cases ha : a ≤ acut q
    · by_cases hτ : tauN Ps w * (a + 1) = T
      · have hK : Kept Ps TM acut w := ⟨by omega, hE⟩
        have hK' : Kept (insert q Ps) TM acut (Function.update w q a) :=
          (kept_insert_update hq TM acut w a).2 ⟨by omega, ha, hE⟩
        simp [hτ, hK, hK', ha]
      · simp [hτ, ha]
    · have hK' : ¬ Kept (insert q Ps) TM acut (Function.update w q a) := fun h =>
        ha ((kept_insert_update hq TM acut w a).1 h).2.1
      simp [hK', ha]
  · have hK' : ¬ Kept (insert q Ps) TM acut (Function.update w q a) := fun h =>
      hE ((kept_insert_update hq TM acut w a).1 h).2.2
    have hK : ¬ Kept Ps TM acut w := fun h => hE h.2
    simp [hK', hK]

/-- Extending/shrinking a range of summation over which the summand vanishes. -/
theorem sum_range_eq_of_vanish {f : ℕ → ℝ} {n n' : ℕ} (hle : n ≤ n')
    (h : ∀ a, n ≤ a → a < n' → f a = 0) :
    ∑ a ∈ range n', f a = ∑ a ∈ range n, f a := by
  symm
  refine sum_subset (range_mono hle) fun a ha hna => ?_
  exact h a (by simpa using hna) (mem_range.1 ha)

/-- Exchanging the cap range `a ≤ γ q` for the truncation range `a ≤ acut q`
(`ρ(a) = 0` for `a > γ q`). -/
theorem sum_rho_ite_eq {q : ℕ} {νq : ℝ} {γq ac : ℕ} (S : ℕ → ℝ) :
    ∑ a ∈ range (γq + 1), rho q νq γq a * (if a ≤ ac then S a else 0) =
      ∑ a ∈ range (ac + 1), rho q νq γq a * S a := by
  have e1 : ∑ a ∈ range (γq + 1), rho q νq γq a * (if a ≤ ac then S a else 0) =
      ∑ a ∈ range (γq + ac + 2), rho q νq γq a * (if a ≤ ac then S a else 0) :=
    (sum_range_eq_of_vanish (by omega) fun a h1 _ => by
      rw [rho_of_gt (by omega), zero_mul]).symm
  have e2 : ∑ a ∈ range (γq + ac + 2), rho q νq γq a * (if a ≤ ac then S a else 0) =
      ∑ a ∈ range (ac + 1), rho q νq γq a * S a := by
    rw [sum_range_eq_of_vanish (f := fun a => rho q νq γq a * (if a ≤ ac then S a else 0))
      (n := ac + 1) (by omega) fun a h1 _ => by simp [show ¬ a ≤ ac by omega]]
    refine sum_congr rfl fun a ha => ?_
    rw [ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 ha))]
  rw [e1, ← e2]

/-- **The DP step** (exact, every cap): for `q ∉ Ps` and `T ≤ TM`,
`P_{Ps ∪ {q}}(τ = T, kept) = Σ_{t ≤ TM} Σ_{a ≤ acut q} [t (a+1) = T] P_{Ps}(τ = t, kept) ρ_q(a)`. -/
theorem lawKept_insert {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ)
    {T : ℕ} (hT : T ≤ TM) :
    lawKept (insert q Ps) ν γ TM acut T =
      ∑ t ∈ range (TM + 1), ∑ a ∈ range (acut q + 1),
        if t * (a + 1) = T then lawKept Ps ν γ TM acut t * rho q (ν q) (γ q) a else 0 := by
  unfold lawKept
  rw [expect_insert hq]
  simp_rw [ind_kept_insert_update hq acut hT]
  have h2 : ∀ a, expect Ps ν γ (fun w => if a ≤ acut q then
        ∑ t ∈ range (TM + 1), (if tauN Ps w = t ∧ Kept Ps TM acut w then (1 : ℝ) else 0) *
          (if t * (a + 1) = T then 1 else 0) else 0) =
      if a ≤ acut q then ∑ t ∈ range (TM + 1),
        expect Ps ν γ (fun w => if tauN Ps w = t ∧ Kept Ps TM acut w then 1 else 0) *
          (if t * (a + 1) = T then 1 else 0) else 0 := by
    intro a
    split_ifs
    · rw [expect_sum]
      exact sum_congr rfl fun t _ => expect_mul_const _ _
    · exact expect_const Ps ν γ 0
  simp_rw [h2]
  rw [sum_rho_ite_eq]
  simp_rw [mul_sum]
  refine sum_comm.trans (sum_congr rfl fun t _ => sum_congr rfl fun a _ => ?_)
  split_ifs <;> ring

/-- The DP step with **upper** bounds: `D ≥ P_old(τ = ·, kept)` on `[0, TM]` and `ℓ ≥ ρ_q` on
`[0, acut q]` give `Σ_{t,a} [t (a+1) = T] D t ℓ a ≥ P_new(τ = T, kept)`. -/
theorem lawKept_insert_le {q : ℕ} (hq : q ∉ Ps) (hν : ∀ r ∈ insert q Ps, 0 ≤ ν r ∧ ν r ≤ r)
    (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ) (D ℓ : ℕ → ℝ)
    (hD : ∀ t ≤ TM, lawKept Ps ν γ TM acut t ≤ D t)
    (hℓ : ∀ a ≤ acut q, rho q (ν q) (γ q) a ≤ ℓ a) {T : ℕ} (hT : T ≤ TM) :
    lawKept (insert q Ps) ν γ TM acut T ≤
      ∑ t ∈ range (TM + 1), ∑ a ∈ range (acut q + 1),
        if t * (a + 1) = T then D t * ℓ a else 0 := by
  rw [lawKept_insert hq ν γ TM acut hT]
  have hν' : ∀ r ∈ Ps, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
  have hνq := hν q (mem_insert_self q Ps)
  refine sum_le_sum fun t ht => sum_le_sum fun a ha => ?_
  split_ifs
  · have ht' := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have ha' := Nat.lt_succ_iff.1 (mem_range.1 ha)
    exact mul_le_mul (hD t ht') (hℓ a ha') (rho_nonneg hνq.1 hνq.2 _ _)
      ((lawKept_nonneg hν' γ TM acut t).trans (hD t ht'))
  · exact le_rfl

/-- The DP step with **lower** bounds: `0 ≤ D ≤ P_old(τ = ·, kept)` on `[0, TM]` and
`0 ≤ ℓ ≤ ρ_q` on `[0, acut q]` give `Σ_{t,a} [t (a+1) = T] D t ℓ a ≤ P_new(τ = T, kept)`. -/
theorem le_lawKept_insert {q : ℕ} (hq : q ∉ Ps) (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ)
    (D ℓ : ℕ → ℝ) (hD0 : ∀ t ≤ TM, 0 ≤ D t) (hD : ∀ t ≤ TM, D t ≤ lawKept Ps ν γ TM acut t)
    (hℓ0 : ∀ a ≤ acut q, 0 ≤ ℓ a) (hℓ : ∀ a ≤ acut q, ℓ a ≤ rho q (ν q) (γ q) a) {T : ℕ}
    (hT : T ≤ TM) :
    ∑ t ∈ range (TM + 1), ∑ a ∈ range (acut q + 1),
        (if t * (a + 1) = T then D t * ℓ a else 0) ≤ lawKept (insert q Ps) ν γ TM acut T := by
  rw [lawKept_insert hq ν γ TM acut hT]
  refine sum_le_sum fun t ht => sum_le_sum fun a ha => ?_
  split_ifs
  · have ht' := Nat.lt_succ_iff.1 (mem_range.1 ht)
    have ha' := Nat.lt_succ_iff.1 (mem_range.1 ha)
    exact mul_le_mul (hD t ht') (hℓ a ha') (hℓ0 a ha') ((hD0 t ht').trans (hD t ht'))
  · exact le_rfl

/-! ### The lost-mass recursion -/

/-- The truncation threshold of the exponent of the new prime for a kept path with partial
`τ = t`: the path is lost at this step iff `v_q ≥ lostThr TM ac t = min(⌊TM/t⌋, ac + 1)`. -/
def lostThr (TM ac t : ℕ) : ℕ := min (TM / t) (ac + 1)

theorem lostThr_le_iff {TM ac t a : ℕ} (ht : 0 < t) :
    lostThr TM ac t ≤ a ↔ ¬ (t * (a + 1) ≤ TM ∧ a ≤ ac) := by
  unfold lostThr
  rw [min_le_iff, not_and_or, not_le, not_le]
  have : TM / t ≤ a ↔ TM < t * (a + 1) := by
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ht, mul_comm]
  rw [this]
  omega

theorem one_le_lostThr {TM ac t : ℕ} (ht : 1 ≤ t) (htTM : t ≤ TM) : 1 ≤ lostThr TM ac t := by
  unfold lostThr
  refine le_min ?_ (Nat.succ_pos ac)
  exact (Nat.one_le_div_iff (by omega)).2 htTM

/-- `h_γ(A) = E_γ[(v+1) 1{v ≥ A}]` for one prime. -/
noncomputable def hMass (q : ℕ) (νq : ℝ) (γq A : ℕ) : ℝ :=
  expect1 q νq γq (fun a => if A ≤ a then (a : ℝ) + 1 else 0)

/-- Pointwise form of the lost-mass recursion. -/
theorem lost_insert_update {q : ℕ} (hq : q ∉ Ps) (TM : ℕ) (acut : ℕ → ℕ) (w : ℕ → ℕ)
    (a : ℕ) :
    (if Kept (insert q Ps) TM acut (Function.update w q a) then (0 : ℝ)
      else (tauN (insert q Ps) (Function.update w q a) : ℝ)) =
      ((a : ℝ) + 1) * (if Kept Ps TM acut w then 0 else (tauN Ps w : ℝ)) +
      ∑ t ∈ range (TM + 1), (if tauN Ps w = t ∧ Kept Ps TM acut w then (1 : ℝ) else 0) *
        ((t : ℝ) * (if lostThr TM (acut q) t ≤ a then (a : ℝ) + 1 else 0)) := by
  rw [sum_ind_kept_mul Ps TM acut w
    (fun t => (t : ℝ) * (if lostThr TM (acut q) t ≤ a then (a : ℝ) + 1 else 0)),
    tauN_insert_update hq]
  push_cast
  by_cases hK : Kept Ps TM acut w
  · have hpos := tauN_pos Ps w
    by_cases hl : lostThr TM (acut q) (tauN Ps w) ≤ a
    · have hK' : ¬ Kept (insert q Ps) TM acut (Function.update w q a) := by
        intro h
        rw [kept_insert_update hq] at h
        exact (lostThr_le_iff hpos).1 hl ⟨h.1, h.2.1⟩
      simp [hK, hK', hl]
    · have hK' : Kept (insert q Ps) TM acut (Function.update w q a) := by
        rw [kept_insert_update hq]
        have := not_not.1 (mt (lostThr_le_iff hpos).2 hl)
        exact ⟨this.1, this.2, hK.2⟩
      simp [hK, hK', hl]
  · have hK' : ¬ Kept (insert q Ps) TM acut (Function.update w q a) := by
      intro h
      rw [kept_insert_update hq] at h
      apply hK
      refine ⟨le_trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos a)) h.1, h.2.2⟩
    simp [hK, hK']
    ring

/-- **The lost-mass recursion** (exact, every cap): for `q ∉ Ps`,
`E_new[τ; lost] = E_old[τ; lost] · E_q[v+1] + Σ_{t ≤ TM} P_old(τ = t, kept) · t · h_γ(A_t)`,
with `A_t = lostThr TM (acut q) t = min(⌊TM/t⌋, acut q + 1)`. -/
theorem lostMass_insert {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ)
    (acut : ℕ → ℕ) :
    lostMass (insert q Ps) ν γ TM acut =
      lostMass Ps ν γ TM acut * expect1 q (ν q) (γ q) (fun a => (a : ℝ) + 1) +
      ∑ t ∈ range (TM + 1), lawKept Ps ν γ TM acut t * (t : ℝ) *
        hMass q (ν q) (γ q) (lostThr TM (acut q) t) := by
  rw [lostMass, expect_insert hq]
  simp_rw [lost_insert_update hq TM acut]
  have h2 : ∀ a : ℕ, expect Ps ν γ (fun w => ((a : ℝ) + 1) *
        (if Kept Ps TM acut w then 0 else (tauN Ps w : ℝ)) +
        ∑ t ∈ range (TM + 1), (if tauN Ps w = t ∧ Kept Ps TM acut w then (1 : ℝ) else 0) *
          ((t : ℝ) * (if lostThr TM (acut q) t ≤ a then (a : ℝ) + 1 else 0))) =
      ((a : ℝ) + 1) * lostMass Ps ν γ TM acut + ∑ t ∈ range (TM + 1),
        lawKept Ps ν γ TM acut t * ((t : ℝ) *
          (if lostThr TM (acut q) t ≤ a then (a : ℝ) + 1 else 0)) := by
    intro a
    rw [expect_add, expect_const_mul, expect_sum]
    congr 1
    exact sum_congr rfl fun t _ => expect_mul_const _ _
  simp_rw [h2]
  simp only [mul_add, sum_add_distrib]
  congr 1
  · unfold expect1
    rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  · unfold hMass expect1
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun t _ => sum_congr rfl fun a _ => by ring

/-- The lost-mass recursion with upper bounds: `L ≥ E_old[τ; lost]`, `D ≥ P_old(τ = ·, kept)`
on `[0, TM]`, `e ≥ E_q[v+1]`, and `H(A_t) ≥ h_γ(A_t)` for `1 ≤ t ≤ TM` give
`L e + Σ_{t ≤ TM} D t · t · H(A_t) ≥ E_new[τ; lost]`. -/
theorem lostMass_insert_le {q : ℕ} (hq : q ∉ Ps) (hν : ∀ r ∈ insert q Ps, 0 ≤ ν r ∧ ν r ≤ r)
    (γ : ℕ → ℕ) (TM : ℕ) (acut : ℕ → ℕ) (L e : ℝ) (D H : ℕ → ℝ)
    (hL : lostMass Ps ν γ TM acut ≤ L) (hD : ∀ t ≤ TM, lawKept Ps ν γ TM acut t ≤ D t)
    (he : expect1 q (ν q) (γ q) (fun a => (a : ℝ) + 1) ≤ e)
    (hH : ∀ t, 1 ≤ t → t ≤ TM → hMass q (ν q) (γ q) (lostThr TM (acut q) t) ≤
      H (lostThr TM (acut q) t)) :
    lostMass (insert q Ps) ν γ TM acut ≤
      L * e + ∑ t ∈ range (TM + 1), D t * (t : ℝ) * H (lostThr TM (acut q) t) := by
  rw [lostMass_insert hq ν γ TM acut]
  have hν' : ∀ r ∈ Ps, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
  have hνq := hν q (mem_insert_self q Ps)
  have hE0 : 0 ≤ expect1 q (ν q) (γ q) (fun a => (a : ℝ) + 1) :=
    expect1_nonneg hνq.1 hνq.2 fun a _ => by positivity
  have hhM0 : ∀ A, 0 ≤ hMass q (ν q) (γ q) A := fun A =>
    expect1_nonneg hνq.1 hνq.2 fun a _ => by split_ifs <;> positivity
  refine add_le_add ?_ (sum_le_sum fun t ht => ?_)
  · exact mul_le_mul hL he hE0 ((lostMass_nonneg hν' γ TM acut).trans hL)
  · have ht' := Nat.lt_succ_iff.1 (mem_range.1 ht)
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · simp
    · have h1 : lawKept Ps ν γ TM acut t * (t : ℝ) ≤ D t * (t : ℝ) :=
        mul_le_mul_of_nonneg_right (hD t ht') (by positivity)
      have h0 : 0 ≤ lawKept Ps ν γ TM acut t * (t : ℝ) :=
        mul_nonneg (lawKept_nonneg hν' γ TM acut t) (by positivity)
      exact mul_le_mul h1 (hH t ht0 ht') (hhM0 _) (h0.trans h1)

/-! ### One-prime bounds, uniform in the cap -/

theorem inv_div_one_sub_inv {q : ℕ} (hq : 1 < q) :
    (q : ℝ)⁻¹ / (1 - (q : ℝ)⁻¹) = 1 / ((q : ℝ) - 1) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq1' : (q : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- `Σ_{r < n} x^{r+1} ≤ x/(1-x)` for `0 ≤ x < 1`. -/
theorem sum_range_pow_succ_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ r ∈ range n, x ^ (r + 1) ≤ x / (1 - x) := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hx0 hx1
  rw [← range_eq_Ico, pow_zero] at h
  have e : ∑ r ∈ range n, x ^ (r + 1) = x * ∑ r ∈ range n, x ^ r := by
    rw [mul_sum]
    exact sum_congr rfl fun r _ => pow_succ' x r
  rw [e, div_eq_mul_one_div x]
  exact mul_le_mul_of_nonneg_left h hx0

/-- `E_γ[v + 1] ≤ 1 + ν/(q - 1)`, for every cap `γ` (`= 1 + Σ_{j=1}^{γ} ν q^{-j}`). -/
theorem expect1_add_one_le {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) (γ : ℕ) :
    expect1 q ν γ (fun a => (a : ℝ) + 1) ≤ 1 + ν / ((q : ℝ) - 1) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have hx1 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  rw [expect1_eq_geom]
  have e : ∑ r ∈ range γ, ((q : ℝ)⁻¹) ^ (r + 1) * ((((r + 1 : ℕ) : ℝ) + 1) - ((r : ℝ) + 1)) =
      ∑ r ∈ range γ, ((q : ℝ)⁻¹) ^ (r + 1) := by
    refine sum_congr rfl fun r _ => ?_
    push_cast
    ring
  rw [e]
  have h := mul_le_mul_of_nonneg_left (sum_range_pow_succ_le hx0 hx1 γ) hν
  rw [inv_div_one_sub_inv hq] at h
  simp only [Nat.cast_zero, zero_add]
  have : ν * (1 / ((q : ℝ) - 1)) = ν / ((q : ℝ) - 1) := by ring
  linarith

/-- Exact partial tail for `h`: for `A ≥ 1`,
`Σ_{r<γ} x^{r+1}(g(r+1) - g(r)) = [A ≤ γ] (x^A (A+1) + Σ_{j ∈ [A+1, γ]} x^j)`
where `g(a) = (a+1) 1{a ≥ A}`. -/
theorem hTail_eq {x : ℝ} {A : ℕ} (hA : 1 ≤ A) (γ : ℕ) :
    ∑ r ∈ range γ, x ^ (r + 1) * ((if A ≤ r + 1 then ((r + 1 : ℕ) : ℝ) + 1 else 0) -
        (if A ≤ r then (r : ℝ) + 1 else 0)) =
      if γ < A then 0 else x ^ A * ((A : ℝ) + 1) + ∑ j ∈ Ico (A + 1) (γ + 1), x ^ j := by
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
        ite_eq_right (by omega), sum_Ico_succ_top (by omega : A + 1 ≤ γ + 1)]
      push_cast
      ring

/-- **`h(A)` bound**, uniform in the cap: for `A ≥ 1`,
`h_γ(A) = E_γ[(v+1) 1{v ≥ A}] ≤ ν q^{-A} (A + 1 + 1/(q-1))`. -/
theorem expect1_hA_le {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) {A : ℕ} (hA : 1 ≤ A)
    (γ : ℕ) :
    hMass q ν γ A ≤ ν * ((q : ℝ)⁻¹) ^ A * ((A : ℝ) + 1 + 1 / ((q : ℝ) - 1)) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 ≤ (q : ℝ)⁻¹ := by positivity
  have hx1 : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  unfold hMass
  rw [expect1_eq_geom]
  have hg0 : (if A ≤ 0 then ((0 : ℕ) : ℝ) + 1 else 0) = 0 := ite_eq_right (by omega)
  simp only [hg0, zero_add]
  rw [hTail_eq hA γ]
  have hxA : 0 ≤ ((q : ℝ)⁻¹) ^ A := pow_nonneg hx0 A
  have hq1' : 0 < (q : ℝ) - 1 := by linarith
  split_ifs
  · rw [mul_zero]
    have : 0 ≤ (A : ℝ) + 1 + 1 / ((q : ℝ) - 1) := by positivity
    positivity
  · have hgeo := geom_sum_Ico_le_of_lt_one (m := A + 1) (n := γ + 1) hx0 hx1
    have e : ((q : ℝ)⁻¹) ^ (A + 1) / (1 - (q : ℝ)⁻¹) =
        ((q : ℝ)⁻¹) ^ A * (1 / ((q : ℝ) - 1)) := by
      rw [pow_succ, mul_div_assoc, inv_div_one_sub_inv hq]
    rw [e] at hgeo
    have := mul_le_mul_of_nonneg_left hgeo hν
    nlinarith

/-- The cap-uniform `h` bound in the form used by `lostMass_insert_le`. -/
theorem hMass_le_lostThr {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) {TM ac t : ℕ} (ht : 1 ≤ t)
    (htTM : t ≤ TM) (γ : ℕ) :
    hMass q ν γ (lostThr TM ac t) ≤ ν * ((q : ℝ)⁻¹) ^ (lostThr TM ac t) *
      ((lostThr TM ac t : ℝ) + 1 + 1 / ((q : ℝ) - 1)) :=
  expect1_hA_le hq hν (one_le_lostThr ht htTM) γ

/-- `E_γ[τ] ≤ ∏_{q ∈ Ps} (1 + ν_q/(q-1))` for every cap `γ`. -/
theorem expect_tauN_le (hPs : ∀ q ∈ Ps, 1 < q) (hν : ∀ q ∈ Ps, 0 ≤ ν q) (γ : ℕ → ℕ) :
    expect Ps ν γ (fun v => (tauN Ps v : ℝ)) ≤ ∏ q ∈ Ps, (1 + ν q / ((q : ℝ) - 1)) := by
  simp_rw [tauN_cast]
  rw [expect_prod Ps ν γ (fun q a => (a : ℝ) + 1)]
  refine prod_le_prod₀ (fun q hq => ?_) fun q hq => expect1_add_one_le (hPs q hq) (hν q hq) (γ q)
  rw [expect1_eq_geom]
  have : 0 ≤ ν q * ∑ r ∈ range (γ q), ((q : ℝ)⁻¹) ^ (r + 1) *
      ((((r + 1 : ℕ) : ℝ) + 1) - ((r : ℝ) + 1)) :=
    mul_nonneg (hν q hq) (sum_nonneg fun r _ => mul_nonneg (by positivity) (by push_cast; linarith))
  simp only [Nat.cast_zero, zero_add]
  linarith

/-! ### Exponent truncation: union bound -/

/-- Marginal of one coordinate: `E_{Ps}[f(v q)] = E_q[f]` for `q ∈ Ps`. -/
theorem expect_coord {q : ℕ} (hq : q ∈ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (f : ℕ → ℝ) :
    expect Ps ν γ (fun v => f (v q)) = expect1 q (ν q) (γ q) f := by
  rw [expect_eq_of_subset (singleton_subset_iff.2 hq) ν γ (f := fun v => f (v q))
    fun v w h => by rw [h q (mem_singleton_self q)], expect_singleton]
  simp

/-- `P_γ(v_q > ac) ≤ ν q^{-(ac+1)}` for every cap. -/
theorem expect1_gt_le {q : ℕ} {ν : ℝ} (hν : 0 ≤ ν) (γ ac : ℕ) :
    expect1 q ν γ (fun a => if ac < a then (1 : ℝ) else 0) ≤ ν * ((q : ℝ)⁻¹) ^ (ac + 1) := by
  have e : (fun a => if ac < a then (1 : ℝ) else 0) = fun a => if ac + 1 ≤ a then 1 else 0 := by
    funext a
    by_cases h : ac < a
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  rw [e]
  by_cases h : ac + 1 ≤ γ
  · rw [expect1_indicator h, tailP_succ]
  · rw [expect1_indicator_of_lt (by omega)]
    exact mul_nonneg hν (pow_nonneg (by positivity) _)

/-- **Union bound** for the exponent truncation:
`P(∃ q ∈ Ps, v q > acut q) ≤ Σ_{q ∈ Ps} ν_q q^{-(acut q + 1)}`, every cap. -/
theorem expLostProb_le (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (acut : ℕ → ℕ) :
    expLostProb Ps ν γ acut ≤ ∑ q ∈ Ps, ν q * ((q : ℝ)⁻¹) ^ (acut q + 1) := by
  unfold expLostProb
  have hpt : ∀ v : ℕ → ℕ, (if ∃ q ∈ Ps, acut q < v q then (1 : ℝ) else 0) ≤
      ∑ q ∈ Ps, (if acut q < v q then (1 : ℝ) else 0) := by
    intro v
    split_ifs with h
    · obtain ⟨q, hq, hlt⟩ := h
      have := single_le_sum (f := fun r => if acut r < v r then (1 : ℝ) else 0)
        (fun r _ => by split_ifs <;> norm_num) hq
      simpa [hlt] using this
    · exact sum_nonneg fun r _ => by split_ifs <;> norm_num
  refine (expect_mono hν fun v _ => hpt v).trans ?_
  rw [expect_sum]
  refine sum_le_sum fun q hq => ?_
  rw [expect_coord hq ν γ (fun a => if acut q < a then (1 : ℝ) else 0)]
  exact expect1_gt_le (hν q hq).1 (γ q) (acut q)

/-! ### Caps -/

/-- Below the cap, `ρ` is the untruncated point mass used by the checkers:
`ρ(q, ν, γ, a) = 1 - ν/q` (`a = 0`), `ν q^{-a} (1 - 1/q)` (`a ≥ 1`), for `a < γ`. -/
theorem rho_eq_pointMass {q : ℕ} {ν : ℝ} {γ a : ℕ} (h : a < γ) :
    rho q ν γ a = if a = 0 then 1 - ν / q else ν * ((q : ℝ)⁻¹) ^ a * (1 - (q : ℝ)⁻¹) := by
  split_ifs with ha
  · subst ha
    exact rho_zero_of_pos h
  · exact rho_of_pos_of_lt (Nat.pos_of_ne_zero ha) h

/-- The lost mass `E_γ[τ; lost]` is nondecreasing in the caps (monotone coupling:
`v ↦ τ(v) 1{v lost}` is nondecreasing). -/
theorem lostMass_mono_cap (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) {γ γ' : ℕ → ℕ}
    (hγ : ∀ q ∈ Ps, γ q ≤ γ' q) (TM : ℕ) (acut : ℕ → ℕ) :
    lostMass Ps ν γ TM acut ≤ lostMass Ps ν γ' TM acut := by
  refine expect_mono_cap hν hγ fun v w hvw => ?_
  have hle : ∀ q ∈ Ps, v q ≤ w q := fun q _ => hvw q
  have hτ : (tauN Ps v : ℝ) ≤ tauN Ps w := by exact_mod_cast tauN_mono Ps hle
  by_cases hKw : Kept Ps TM acut w
  · have hKv : Kept Ps TM acut v :=
      ⟨(tauN_mono Ps hle).trans hKw.1, fun q hq => (hle q hq).trans (hKw.2 q hq)⟩
    simp [hKv, hKw]
  · rw [ite_eq_right hKw]
    split_ifs
    · exact tauN_real_nonneg Ps w
    · exact hτ

/-- **Uniformity over all caps** for the lost mass: a bound valid for every uniform cap
`N ≥ N0` is valid for every uniform cap (`lostMass_mono_cap`). -/
theorem lostMass_le_of_forall_ge (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) (TM : ℕ) (acut : ℕ → ℕ)
    (N0 : ℕ) {L : ℝ} (h : ∀ N, N0 ≤ N → lostMass Ps ν (fun _ => N) TM acut ≤ L) (N : ℕ) :
    lostMass Ps ν (fun _ => N) TM acut ≤ L :=
  (lostMass_mono_cap hν (γ' := fun _ => max N N0) (fun _ _ => le_max_left N N0) TM acut).trans
    (h _ (le_max_right N N0))

/-- For caps above the exponent cut-offs, `P(τ = T, kept)` does not depend on the caps. -/
theorem lawKept_congr_cap {γ γ' : ℕ → ℕ} (hγ : ∀ q ∈ Ps, acut q < γ q)
    (hγ' : ∀ q ∈ Ps, acut q < γ' q) (ν : ℕ → ℝ) (TM T : ℕ) :
    lawKept Ps ν γ TM acut T = lawKept Ps ν γ' TM acut T := by
  induction Ps using Finset.induction_on generalizing T with
  | empty => simp [lawKept, expect_empty]
  | insert q Ps hq ih =>
    have hγ₁ : ∀ r ∈ Ps, acut r < γ r := fun r hr => hγ r (mem_insert_of_mem hr)
    have hγ₁' : ∀ r ∈ Ps, acut r < γ' r := fun r hr => hγ' r (mem_insert_of_mem hr)
    by_cases hT : T ≤ TM
    · rw [lawKept_insert hq ν γ TM acut hT, lawKept_insert hq ν γ' TM acut hT]
      refine sum_congr rfl fun t _ => sum_congr rfl fun a ha => ?_
      have ha' := Nat.lt_succ_iff.1 (mem_range.1 ha)
      rw [ih hγ₁ hγ₁' t, rho_eq_of_lt_of_lt (lt_of_le_of_lt ha' (hγ q (mem_insert_self q Ps)))
        (lt_of_le_of_lt ha' (hγ' q (mem_insert_self q Ps)))]
    · rw [lawKept_of_lt _ ν γ acut (by omega), lawKept_of_lt _ ν γ' acut (by omega)]

/-! ### Pull form of the DP step, and the untruncated law of `τ` -/

/-- Selecting `t = T/(a+1)`: `Σ_{t ≤ TM} [t (a+1) = T] X(t) = [(a+1) ∣ T] X(T/(a+1))` for
`T ≤ TM`. -/
theorem sum_mul_succ_eq {TM T : ℕ} (hT : T ≤ TM) (a : ℕ) (X : ℕ → ℝ) :
    ∑ t ∈ range (TM + 1), (if t * (a + 1) = T then X t else 0) =
      if (a + 1) ∣ T then X (T / (a + 1)) else 0 := by
  have h : ∀ t, (if t * (a + 1) = T then X t else 0) =
      if t = T / (a + 1) then (if (a + 1) ∣ T then X t else 0) else 0 := by
    intro t
    by_cases ht : t * (a + 1) = T
    · have hd : (a + 1) ∣ T := ⟨t, by rw [← ht, mul_comm]⟩
      have ht' : t = T / (a + 1) := by
        rw [← ht, Nat.mul_div_cancel _ (Nat.succ_pos a)]
      rw [ite_eq_left ht, ite_eq_left ht', ite_eq_left hd]
    · by_cases ht' : t = T / (a + 1)
      · have hd : ¬ (a + 1) ∣ T := by
          rintro ⟨c, hc⟩
          apply ht
          rw [ht', hc, Nat.mul_div_cancel_left _ (Nat.succ_pos a), mul_comm]
        simp [ht, hd]
      · simp [ht, ht']
  rw [sum_congr rfl fun t _ => h t, sum_ite_eq']
  have : T / (a + 1) ∈ range (TM + 1) :=
    mem_range.2 (Nat.lt_succ_of_le ((Nat.div_le_self T (a + 1)).trans hT))
  simp only [this, ↓reduceIte]

/-- **The DP step, pull form**: for `q ∉ Ps` and `T ≤ TM`,
`P_new(τ = T, kept) = Σ_{a ≤ acut q, (a+1) ∣ T} P_old(τ = T/(a+1), kept) ρ_q(a)`. -/
theorem lawKept_insert_pull {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (TM : ℕ)
    (acut : ℕ → ℕ) {T : ℕ} (hT : T ≤ TM) :
    lawKept (insert q Ps) ν γ TM acut T =
      ∑ a ∈ range (acut q + 1), if (a + 1) ∣ T then
        lawKept Ps ν γ TM acut (T / (a + 1)) * rho q (ν q) (γ q) a else 0 := by
  rw [lawKept_insert hq ν γ TM acut hT, sum_comm]
  exact sum_congr rfl fun a _ =>
    sum_mul_succ_eq hT a (fun t => lawKept Ps ν γ TM acut t * rho q (ν q) (γ q) a)

/-- The (untruncated) law of `τ`: `P(τ = T)` under the capped tilted law. -/
noncomputable def lawTau (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (T : ℕ) : ℝ :=
  expect Ps ν γ (fun v => if tauN Ps v = T then 1 else 0)

theorem lawTau_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (T : ℕ) :
    lawTau ∅ ν γ T = if T = 1 then 1 else 0 := by
  unfold lawTau
  rw [expect_empty, tauN_empty]
  by_cases hT : T = 1
  · simp [hT]
  · rw [ite_eq_right (fun h => hT h.symm), ite_eq_right hT]

/-- **The multiplicative-convolution recursion** for the exact law of `τ` (every cap):
for `q ∉ Ps`, `P_{Ps ∪ {q}}(τ = T) = Σ_{a ≤ γ q, (a+1) ∣ T} P_{Ps}(τ = T/(a+1)) ρ_q(a)`. -/
theorem lawTau_insert {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (T : ℕ) :
    lawTau (insert q Ps) ν γ T =
      ∑ a ∈ range (γ q + 1), if (a + 1) ∣ T then
        lawTau Ps ν γ (T / (a + 1)) * rho q (ν q) (γ q) a else 0 := by
  unfold lawTau
  rw [expect_insert hq]
  refine sum_congr rfl fun a _ => ?_
  have h : ∀ w, (if tauN (insert q Ps) (Function.update w q a) = T then (1 : ℝ) else 0) =
      if (a + 1) ∣ T then (if tauN Ps w = T / (a + 1) then 1 else 0) else 0 := by
    intro w
    rw [tauN_insert_update hq]
    by_cases hd : (a + 1) ∣ T
    · obtain ⟨c, rfl⟩ := hd
      rw [Nat.mul_div_cancel_left _ (Nat.succ_pos a), mul_comm]
      have : (a + 1) * tauN Ps w = (a + 1) * c ↔ tauN Ps w = c :=
        ⟨fun h => Nat.eq_of_mul_eq_mul_left (Nat.succ_pos a) h, fun h => by rw [h]⟩
      simp [this]
    · have : ¬ tauN Ps w * (a + 1) = T := fun h => hd ⟨tauN Ps w, by rw [← h, mul_comm]⟩
      simp [this, hd]
  simp_rw [h]
  split_ifs
  · ring
  · rw [expect_const, mul_zero]

/-- Without truncation (`TM ≥ T`, `acut ≥ γ`), the kept law is the exact law. -/
theorem lawKept_eq_lawTau {TM T : ℕ} (hT : T ≤ TM) (hac : ∀ q ∈ Ps, γ q ≤ acut q) :
    lawKept Ps ν γ TM acut T = lawTau Ps ν γ T := by
  unfold lawKept lawTau
  refine expect_congr_fun fun v hv => ?_
  by_cases hτ : tauN Ps v = T
  · have hK : Kept Ps TM acut v :=
      ⟨hτ ▸ hT, fun q hq => ((mem_box.1 hv).1 q hq).trans (hac q hq)⟩
    simp [hτ, hK]
  · simp [hτ]

end MinModulus.CheckerMath
