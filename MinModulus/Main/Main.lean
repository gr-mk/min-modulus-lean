import MinModulus.Main.Stubs
import MinModulus.Distortion.Main
import MinModulus.Comparison.Main
import MinModulus.Arith.Main
import MinModulus.Tail.Main
import MinModulus.Smooth.Hinge
import MinModulus.Smooth.Moments

/-!
# Main: assembly of the theorem "least modulus of a distinct covering system ≤ 15,999"

STATUS: complete, no `sorry`. The numeric certificate `Stub.cert_16000` (`Main/Stubs.lean`) is
now `CheckerSound.D.cert_16000`: the executable checker `CheckerImpl.check` (evaluated once by
`native_decide`) together with the code-level soundness proof in `CheckerSound/`. All other
modules are imported for real: `Distortion`, `Comparison`, `Arith`, `Tail`, `Smooth`.

## The final theorem
`MinModulus.not_covers`: congruences `a i (mod d i)` with distinct moduli `d i ≥ 16000` do not
cover `ℤ`. It is `not_covers_of_cert` applied to `Stub.cert_16000`.

## The chain (for a certificate `hc : Cert m X δ c T`, see `Main/Certificate.lean`)
1. `Arith`: the setup `S` (`Q = ∏ d_i`, primes `p_0 < … < p_{n-1}` of `Q`, `X_j = ZMod (p_j^γ_j)`,
   levels, `B ℓ`, CRT). A point outside every `B ℓ` gives an uncovered integer
   (`exists_int_of_forall_not_mem_B`).
2. `Distortion.criterion_kernel` with `δ_ℓ = δ(p_ℓ)` (`δL`) and the pointwise majorant
   `max 0 (Σ_i wt_i [x ∈ rect_i] - δ_ℓ)/(1 - δ_ℓ)` (`Arith.hinge_alpha_le`, i.e. α ≤ min(1, U)
   plus the hinge step with `t = δ_ℓ`).
3. Per level `ℓ` (`level_le_aligned`): `Comparison.comparison` (kernels `Distortion.kernel`,
   tilts `Distortion.nu`), then `Comparison.aligned_eq_vLaw`, then the enlargement
   `Arith.enlargement_rect_of_weight` with `W = Smooth.wp`, giving `Smooth.Up` directly.
4. `aligned_eq_expect`: the V-law sum is `Smooth.expect` over the primes `p_j`, `j < ℓ`
   (`below S ℓ`), with tilts `tilt δ` and caps `v_q(Q)` (`capN`): `vLaw = rho`
   (`vLaw_eq_rho`, via `Comparison.vTail_eq_ite`), `Smooth.sum_pi_fin_eq_expect`, marginalization
   (`Smooth.expect_eq_of_subset`) and `Smooth.expect_congr_param`. Result: `levelLoss S δ ℓ`.
5. Levels with `p_ℓ ≤ X` (`levelLoss_le_hingeLoss`): enlarge the set of primes to
   `Nat.primesBelow p_ℓ` (`expect_Up_mono_primes`), then the certificate (b), extended from
   uniform caps to the caps `v_q(Q)` by `Cert.loss_le_all`: `≤ c p_ℓ`.
6. Levels with `p_ℓ > X` (`levelLoss_le_tail`): `δ = 1/2`, `(u - 1/2)^+/(1/2) ≤ u²`
   (`Smooth.hinge_le_sq_div`), `U ≤ τ/(p-1)` (`Smooth.Up_le_card_div`), `E[τ²] = ∏ E[(v+1)²]`
   (`Smooth.expect_tau_pow`), `E[(v+1)²] ≤ tailFactor` (`Smooth.expect1_sq_le`); the primes
   `≤ X` contribute `≤ T` (certificate (c)); the rest is the Tail product.
7. Sum over levels (`budget`, `level_le_budget`, `sum_budget_lt`): `Σ_{p ≤ X} c p` (costs are
   `≥ 0` by (b), `Cert.cost_nonneg`) plus `T · Tail.tail_bound_family_nu ≤ T · 100/(189 X)`;
   `< 1` by certificate (d). Then `uncovered_of_cert`, `not_covers_of_cert`.

## Interface notes (adapters between the modules; no blocking mismatch was found)
* Comparison ↔ Smooth: `vLaw_eq_rho` (`Comparison.vLaw q ν e r = Smooth.rho q ν e r` for
  `1 ≤ ν ≤ q`, `r ≤ e`); the level tilts `Distortion.nu (δL S δ) ℓ j` are rewritten as the prime
  tilts `nuL S δ ℓ (S.p j)` (`hnu` in `aligned_eq_expect`); caps `capN S (S.p j) ≡ S.γ j` (defeq).
* Arith ↔ Smooth: no `U = Up` bridge is needed: `S.enlargement_rect_of_weight` with
  `W := Smooth.wp (S.p ℓ) S.m` and `Smooth.sum_le_wp` yields `Smooth.Up` by definition.
  `smooth_below`: `∏_{j<ℓ} p_j ^ v (p_j) = Smooth.smooth (below S ℓ) v`.
* Distortion ↔ Arith: `S.B_congr : DependsLE S.B` and `Distortion.alpha S.B = S.alpha` hold
  definitionally; `S.hinge_alpha_le` is the `hh` argument of `criterion_kernel`.
* Distortion ↔ Comparison: `kernel_nonneg`, `kernel_sum`, `kernel_le`, `one_le_nu`, `kernel_dep`
  are exactly `comparison`'s hypotheses.
* Tail: `tail_bound_family_nu` (general `X ≥ 2^27`, constant `100/(189 X)`) is used rather than
  `tail_bound_family_nu_2e8`; its factor `1 + ν_j (3P_j - 1)/(P_j - 1)^2` is literally
  `tailFactor δ (S.p j)` with `ν_j = tilt δ (S.p j)`.
* New generic lemma: `expect_Up_mono_primes` (monotonicity of `E[g(U_p(s))]` in the set of primes).

## Axioms
`not_covers_of_cert`: `propext`, `Classical.choice`, `Quot.sound`. `not_covers` (final audit,
`CheckerSound/Audit.lean`): `propext`, `Classical.choice`, `Quot.sound` and
`MinModulus.CheckerImpl.check_eq_true._native.native_decide.ax_1_1`, which states
`decide (MinModulus.CheckerImpl.check = true) = true`. NOTE (Lean v4.34.1): `native_decide` no
longer goes through `Lean.ofReduceBool` (deprecated); it adds one auxiliary axiom
`<decl>._native.native_decide.ax_N_M : <closed Bool term> = true` per call, i.e. the proof trusts
the compiled evaluation of the checker (about 50 s natively).
-/

namespace MinModulus.Main

open Finset

/-! ## Generic bridges between the modules -/

/-- Comparison's V-law is Smooth's capped law `rho`, for `1 ≤ ν ≤ q` and `r ≤ e`. -/
theorem vLaw_eq_rho {q e r : ℕ} {ν : ℝ} (hq : 1 ≤ q) (hν : 1 ≤ ν) (hνq : ν ≤ q) (hr : r ≤ e) :
    Comparison.vLaw q ν e r = Smooth.rho q ν e r := by
  have h : ∀ k, Comparison.vTail q ν k = Smooth.tailP q ν k := fun k => by
    rw [Comparison.vTail_eq_ite hq hν hνq]
    rfl
  unfold Comparison.vLaw Smooth.rho
  rcases hr.lt_or_eq with hlt | rfl
  · rw [ite_eq_left hlt, ite_eq_left hlt, h, h]
  · rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _), ite_eq_left rfl, h]

/-- Monotonicity in the set of primes: for `A ⊆ B` (primes) and `g` nondecreasing,
`E_A[g(U_p(s_A))] ≤ E_B[g(U_p(s_B))]`. -/
theorem expect_Up_mono_primes {A B : Finset ℕ} (hAB : A ⊆ B) (hB : ∀ q ∈ B, q.Prime)
    {ν : ℕ → ℝ} (hν : ∀ q ∈ B, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) {p m : ℕ} (hp : 1 < p)
    {g : ℝ → ℝ} (hg : Monotone g) :
    Smooth.expect A ν γ (fun v => g (Smooth.Up p m (Smooth.smooth A v))) ≤
      Smooth.expect B ν γ (fun v => g (Smooth.Up p m (Smooth.smooth B v))) := by
  rw [← Smooth.expect_eq_of_subset hAB ν γ
    (f := fun v => g (Smooth.Up p m (Smooth.smooth A v))) fun v w h => by
      simp only [Smooth.smooth]
      rw [prod_congr rfl fun q hq => by rw [h q hq]]]
  refine Smooth.expect_mono hν fun v _ => hg ?_
  exact Smooth.Up_mono hp m (prod_dvd_prod_of_subset A B _ hAB)
    (Smooth.smooth_ne_zero (fun q hq => (hB q hq).pos) v)

/-! ## Levels -/

section Levels

variable {ι : Type*} [Fintype ι] (S : Arith.Setup ι)

/-- The distortion parameter of level `ℓ`: `δ_ℓ = δ(p_ℓ)`. -/
noncomputable def δL (δ : ℕ → ℝ) (ℓ : Fin S.n) : ℝ := δ (S.p ℓ)

/-- The caps as a function on the primes: `γ_q = v_q(Q)` (so `capN S (S.p j) = S.γ j`). -/
noncomputable def capN (q : ℕ) : ℕ := S.Q.factorization q

/-- The primes `p_j`, `j < ℓ`: the primes of `Q` below `p_ℓ`. -/
def below (ℓ : Fin S.n) : Finset ℕ := (univ.filter (· < ℓ)).image S.p

/-- The tilts of the level-`ℓ` measure, on primes: `tilt δ q` below `p_ℓ`, `1` from `p_ℓ` on. -/
noncomputable def nuL (δ : ℕ → ℝ) (ℓ : Fin S.n) (q : ℕ) : ℝ :=
  if q < S.p ℓ then tilt δ q else 1

/-- The loss bound at level `ℓ`: `E[max 0 (U_{p_ℓ}(s) - δ(p_ℓ)) / (1 - δ(p_ℓ))]` over the primes
of `Q` below `p_ℓ`, caps `v_q(Q)`, tilts `tilt δ`. -/
noncomputable def levelLoss (δ : ℕ → ℝ) (ℓ : Fin S.n) : ℝ :=
  Smooth.expect (below S ℓ) (tilt δ) (capN S)
    (fun v => max 0 (Smooth.Up (S.p ℓ) S.m (Smooth.smooth (below S ℓ) v) - δ (S.p ℓ)) /
      (1 - δ (S.p ℓ)))

/-- The levels whose prime exceeds the tail threshold `X`. -/
def tailSet (X : ℕ) : Finset (Fin S.n) := univ.filter fun j => ¬ S.p j ≤ X

theorem mem_below {ℓ : Fin S.n} {q : ℕ} : q ∈ below S ℓ ↔ ∃ j, j < ℓ ∧ S.p j = q := by
  simp [below]

theorem prime_of_mem_below {ℓ : Fin S.n} {q : ℕ} (hq : q ∈ below S ℓ) : q.Prime := by
  obtain ⟨j, -, rfl⟩ := (mem_below S).1 hq
  exact S.p_prime j

theorem lt_of_mem_below {ℓ : Fin S.n} {q : ℕ} (hq : q ∈ below S ℓ) : q < S.p ℓ := by
  obtain ⟨j, hj, rfl⟩ := (mem_below S).1 hq
  exact S.p_lt_p_iff.2 hj

theorem below_subset_primesBelow (ℓ : Fin S.n) : below S ℓ ⊆ Nat.primesBelow (S.p ℓ) :=
  fun _ hq => Nat.mem_primesBelow.2 ⟨lt_of_mem_below S hq, prime_of_mem_below S hq⟩

theorem smooth_below (ℓ : Fin S.n) (v : ℕ → ℕ) :
    Smooth.smooth (below S ℓ) v = ∏ j ∈ univ.filter (· < ℓ), S.p j ^ v (S.p j) := by
  unfold Smooth.smooth below
  exact prod_image fun x _ y _ h => S.p_injective h

/-- Step 3: Distortion + Comparison + Arith. The level-`ℓ` loss integrand, integrated against
the kernel form of `P ℓ`, is at most the aligned V-law sum of the hinge of `U_{p_ℓ}`. -/
theorem level_le_aligned (δ : ℕ → ℝ) (hδ0 : ∀ ℓ, 0 ≤ δL S δ ℓ) (hδ1 : ∀ ℓ, δL S δ ℓ < 1)
    (ℓ : Fin S.n) :
    ∑ x, (∏ j, Distortion.kernel S.B (δL S δ) ℓ j x (x j)) *
        (max 0 (∑ i, (if ∀ j, x j ∈ S.rect ℓ i j then S.wt ℓ i else 0) - δL S δ ℓ) /
          (1 - δL S δ ℓ))
      ≤ ∑ v : (j : Fin S.n) → Fin (S.γ j + 1),
          (∏ j, Comparison.vLaw (S.p j) (Distortion.nu (δL S δ) ℓ j) (S.γ j) (v j)) *
            (max 0 (Smooth.Up (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ (v j : ℕ)) -
              δL S δ ℓ) / (1 - δL S δ ℓ)) := by
  have h1t : 0 < 1 - δL S δ ℓ := by linarith [hδ1 ℓ]
  have hν1 : ∀ j, 1 ≤ Distortion.nu (δL S δ) ℓ j := fun j => Distortion.one_le_nu hδ0 hδ1 ℓ j
  simp_rw [← mul_div_assoc]
  rw [← sum_div, ← sum_div]
  apply div_le_div_of_nonneg_right _ h1t.le
  calc _ ≤ _ := Comparison.comparison (Distortion.kernel S.B (δL S δ) ℓ)
            (Distortion.nu (δL S δ) ℓ)
            (fun j x y => Distortion.kernel_nonneg hδ1 ℓ j x y)
            (fun j x => Distortion.kernel_sum hδ0 hδ1 ℓ j x)
            (fun j x y => Distortion.kernel_le hδ0 hδ1 ℓ j x y) hν1
            (fun j x x' h => Distortion.kernel_dep S.B_congr ℓ j x x' h)
            (S.wt ℓ) (S.wt_nonneg ℓ) (S.rect ℓ) (δL S δ ℓ)
    _ = _ := Comparison.aligned_eq_vLaw (Distortion.nu (δL S δ) ℓ)
            (fun j => by linarith [hν1 j])
            S.p S.γ (fun j => (S.p_prime j).one_lt) S.card_X (S.wt ℓ) (S.rect ℓ) (S.rectExp ℓ)
            (S.rectExp_le_γ ℓ) (S.card_rect ℓ) (δL S δ ℓ)
    _ ≤ _ := by
      gcongr with v
      · exact prod_nonneg fun j _ => Comparison.vLaw_nonneg (S.p_prime j).one_lt.le
          (by linarith [hν1 j]) _ _
      · exact S.enlargement_rect_of_weight ℓ (fun j => (v j : ℕ)) (Smooth.wp (S.p ℓ) S.m)
          fun _ hd T hT => Smooth.sum_le_wp (S.p_prime ℓ).one_lt hd T hT

/-- Step 4: the aligned V-law sum is Smooth's expectation over the primes of `Q` below `p_ℓ`. -/
theorem aligned_eq_expect (δ : ℕ → ℝ) (hδ0 : ∀ q, q.Prime → 0 ≤ δ q)
    (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) (ℓ : Fin S.n) (g : ℝ → ℝ) :
    ∑ v : (j : Fin S.n) → Fin (S.γ j + 1),
        (∏ j, Comparison.vLaw (S.p j) (Distortion.nu (δL S δ) ℓ j) (S.γ j) (v j)) *
          g (Smooth.Up (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ (v j : ℕ)))
      = Smooth.expect (below S ℓ) (tilt δ) (capN S)
          (fun v => g (Smooth.Up (S.p ℓ) S.m (Smooth.smooth (below S ℓ) v))) := by
  have hnu : ∀ j, Distortion.nu (δL S δ) ℓ j = nuL S δ ℓ (S.p j) := by
    intro j
    unfold Distortion.nu nuL
    exact if_congr (Fin.lt_def.symm.trans S.p_lt_p_iff.symm) rfl rfl
  have hrange : ∀ q, q.Prime → 1 ≤ nuL S δ ℓ q ∧ nuL S δ ℓ q ≤ q := by
    intro q hq
    unfold nuL
    split_ifs
    · exact ⟨one_le_tilt (hδ0 q hq) (hδ1 q hq), tilt_le_self (hδ1 q hq) hq⟩
    · exact ⟨le_rfl, by exact_mod_cast hq.one_lt.le⟩
  calc ∑ v : (j : Fin S.n) → Fin (S.γ j + 1),
        (∏ j, Comparison.vLaw (S.p j) (Distortion.nu (δL S δ) ℓ j) (S.γ j) (v j)) *
          g (Smooth.Up (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ (v j : ℕ)))
      = ∑ v : (j : Fin S.n) → Fin (S.γ j + 1),
        (∏ j, Smooth.rho (S.p j) (nuL S δ ℓ (S.p j)) (capN S (S.p j)) (v j)) *
          g (Smooth.Up (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ (v j : ℕ))) := by
        refine sum_congr rfl fun v _ => ?_
        congr 1
        refine prod_congr rfl fun j _ => ?_
        rw [hnu j]
        exact vLaw_eq_rho (S.p_prime j).one_lt.le (hrange _ (S.p_prime j)).1
          (hrange _ (S.p_prime j)).2 (Nat.lt_succ_iff.1 (v j).isLt)
    _ = Smooth.expect (univ.image S.p) (nuL S δ ℓ) (capN S)
          (fun v => g (Smooth.Up (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ v (S.p j)))) :=
        Smooth.sum_pi_fin_eq_expect S.p S.p_injective (nuL S δ ℓ) (capN S)
          (fun V => g (Smooth.Up (S.p ℓ) S.m (∏ j ∈ univ.filter (· < ℓ), S.p j ^ V j)))
    _ = Smooth.expect (univ.image S.p) (nuL S δ ℓ) (capN S)
          (fun v => g (Smooth.Up (S.p ℓ) S.m (Smooth.smooth (below S ℓ) v))) := by
        simp only [smooth_below]
    _ = Smooth.expect (below S ℓ) (nuL S δ ℓ) (capN S)
          (fun v => g (Smooth.Up (S.p ℓ) S.m (Smooth.smooth (below S ℓ) v))) :=
        Smooth.expect_eq_of_subset (image_subset_image (filter_subset _ _)) _ _
          fun v w h => by
            simp only [Smooth.smooth]
            rw [prod_congr rfl fun q hq => by rw [h q hq]]
    _ = Smooth.expect (below S ℓ) (tilt δ) (capN S)
          (fun v => g (Smooth.Up (S.p ℓ) S.m (Smooth.smooth (below S ℓ) v))) :=
        Smooth.expect_congr_param (fun q hq => by
            unfold nuL
            rw [ite_eq_left (lt_of_mem_below S hq)])
          (fun _ _ => rfl) _

/-- Steps 2–4 at one level: the Distortion loss integrand at level `ℓ` is `≤ levelLoss`. -/
theorem level_le_levelLoss (δ : ℕ → ℝ) (hδ0 : ∀ q, q.Prime → 0 ≤ δ q)
    (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) (ℓ : Fin S.n) :
    ∑ x, (∏ j, Distortion.kernel S.B (δL S δ) ℓ j x (x j)) *
        (max 0 (∑ i, (if ∀ j, x j ∈ S.rect ℓ i j then S.wt ℓ i else 0) - δL S δ ℓ) /
          (1 - δL S δ ℓ))
      ≤ levelLoss S δ ℓ :=
  (level_le_aligned S δ (fun ℓ => hδ0 _ (S.p_prime ℓ))
    (fun ℓ => (hδ1 _ (S.p_prime ℓ)).trans_lt (by norm_num)) ℓ).trans_eq
    (aligned_eq_expect S δ hδ0 hδ1 ℓ (fun u => max 0 (u - δ (S.p ℓ)) / (1 - δ (S.p ℓ))))

/-- Step 5: for every level, `levelLoss ≤ hingeLoss` (all primes below `p_ℓ`). -/
theorem levelLoss_le_hingeLoss (δ : ℕ → ℝ) (hδ0 : ∀ q, q.Prime → 0 ≤ δ q)
    (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) (ℓ : Fin S.n) :
    levelLoss S δ ℓ ≤ hingeLoss S.m δ (S.p ℓ) (capN S) := by
  have h1 : 0 < 1 - δ (S.p ℓ) := by linarith [hδ1 _ (S.p_prime ℓ)]
  unfold levelLoss hingeLoss
  exact expect_Up_mono_primes (below_subset_primesBelow S ℓ)
    (fun q hq => Nat.prime_of_mem_primesBelow hq)
    (fun q hq => tilt_mem hδ0 hδ1 (Nat.prime_of_mem_primesBelow hq)) (capN S)
    (S.p_prime ℓ).one_lt (g := fun u => max 0 (u - δ (S.p ℓ)) / (1 - δ (S.p ℓ)))
    fun a b hab => div_le_div_of_nonneg_right (max_le_max le_rfl (sub_le_sub_right hab _)) h1.le

/-- Step 6: the levels beyond the tail threshold. -/
theorem levelLoss_le_tail {X : ℕ} {δ : ℕ → ℝ} {T : ℝ} (hδ0 : ∀ q, q.Prime → 0 ≤ δ q)
    (hδ1 : ∀ q, q.Prime → δ q ≤ 1 / 2) (hδX : ∀ p, p.Prime → X < p → δ p = 1 / 2)
    (hT : ∏ q ∈ Nat.primesLE X, tailFactor δ q ≤ T) (ℓ : Fin S.n) (hℓ : X < S.p ℓ) :
    levelLoss S δ ℓ ≤
      T * (∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j)) / ((S.p ℓ : ℝ) - 1) ^ 2 := by
  have hp := S.p_prime ℓ
  have hp1 : (1 : ℝ) < S.p ℓ := by exact_mod_cast hp.one_lt
  have hδp : δ (S.p ℓ) = 1 / 2 := hδX _ hp hℓ
  have hA : ∀ q ∈ below S ℓ, q.Prime := fun q hq => prime_of_mem_below S hq
  have hνA : ∀ q ∈ below S ℓ, 0 ≤ tilt δ q ∧ tilt δ q ≤ q := fun q hq =>
    tilt_mem hδ0 hδ1 (hA q hq)
  have htF : ∀ q, q.Prime → 1 ≤ tailFactor δ q := fun q hq =>
    one_le_tailFactor (hδ0 q hq) (hδ1 q hq) hq.one_lt.le
  set C : ℝ := 1 / ((S.p ℓ : ℝ) - 1) ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  -- pointwise: hinge at `1/2` ≤ `U²` ≤ `τ² / (p - 1)²`
  have step1 : levelLoss S δ ℓ ≤ Smooth.expect (below S ℓ) (tilt δ) (capN S)
      (fun v => ((Smooth.smooth (below S ℓ) v).divisors.card : ℝ) ^ 2 * C) := by
    unfold levelLoss
    rw [hδp]
    refine Smooth.expect_mono hνA fun v _ => ?_
    set u := Smooth.Up (S.p ℓ) S.m (Smooth.smooth (below S ℓ) v)
    have hu0 : 0 ≤ u := Smooth.Up_nonneg hp.one_lt _ _
    have hu : u ≤ ((Smooth.smooth (below S ℓ) v).divisors.card : ℝ) / ((S.p ℓ : ℝ) - 1) :=
      Smooth.Up_le_card_div hp.one_lt _ _
    have hh := Smooth.hinge_le_sq_div (t := 1 / 2) (by norm_num) u
    have hsq : u ^ 2 ≤ (((Smooth.smooth (below S ℓ) v).divisors.card : ℝ) /
        ((S.p ℓ : ℝ) - 1)) ^ 2 := pow_le_pow_left₀ hu0 hu 2
    rw [div_pow] at hsq
    calc max 0 (u - 1 / 2) / (1 - 1 / 2) ≤ u ^ 2 := by
          rw [div_le_iff₀ (by norm_num)]
          linarith
      _ ≤ _ := hsq
      _ = _ := by rw [hC, div_eq_mul_one_div]
  -- factorization of `E[τ²]` and the moment bound
  have step2 : Smooth.expect (below S ℓ) (tilt δ) (capN S)
      (fun v => ((Smooth.smooth (below S ℓ) v).divisors.card : ℝ) ^ 2 * C) ≤
      (∏ q ∈ below S ℓ, tailFactor δ q) * C := by
    rw [Smooth.expect_mul_const, Smooth.expect_tau_pow hA]
    refine mul_le_mul_of_nonneg_right (prod_le_prod₀ (fun q hq => ?_) fun q hq => ?_) hC0
    · exact Smooth.expect1_nonneg (hνA q hq).1 (hνA q hq).2 fun a _ => by positivity
    · exact Smooth.expect1_sq_le (hA q hq).one_lt (hνA q hq).1 _
  -- split the primes at `X`
  have hsplit : ∏ q ∈ below S ℓ, tailFactor δ q =
      (∏ q ∈ below S ℓ with q ≤ X, tailFactor δ q) *
        ∏ q ∈ below S ℓ with ¬ q ≤ X, tailFactor δ q :=
    (prod_filter_mul_prod_filter_not _ _ _).symm
  have hsmall : ∏ q ∈ below S ℓ with q ≤ X, tailFactor δ q ≤ T := by
    refine le_trans (prod_le_prod_of_subset_of_one_le₀ ?_ ?_ ?_) hT
    · intro q hq
      rw [mem_filter] at hq
      exact Nat.mem_primesLE.2 ⟨hq.2, hA q hq.1⟩
    · intro q hq
      exact zero_le_one.trans (htF q (hA q (mem_filter.1 hq).1))
    · intro q hq _
      exact htF q (Nat.prime_of_mem_primesLE hq)
  have hbig : ∏ q ∈ below S ℓ with ¬ q ≤ X, tailFactor δ q =
      ∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j) := by
    unfold below tailSet
    rw [filter_image, filter_comm, prod_image fun x _ y _ h => S.p_injective h]
  have hbig0 : 0 ≤ ∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j) :=
    prod_nonneg fun j _ => zero_le_one.trans (htF _ (S.p_prime j))
  calc levelLoss S δ ℓ ≤ (∏ q ∈ below S ℓ, tailFactor δ q) * C := step1.trans step2
    _ = (∏ q ∈ below S ℓ with q ≤ X, tailFactor δ q) *
          (∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j)) * C := by rw [hsplit, hbig]
    _ ≤ T * (∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j)) * C := by
        gcongr
    _ = T * (∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j)) /
          ((S.p ℓ : ℝ) - 1) ^ 2 := by rw [hC, mul_one_div]

/-- The per-level budget: `c p_ℓ` for `p_ℓ ≤ X`, the tail term otherwise. -/
noncomputable def budget (X : ℕ) (δ c : ℕ → ℝ) (T : ℝ) (ℓ : Fin S.n) : ℝ :=
  if S.p ℓ ≤ X then c (S.p ℓ) else
    T * (∏ j ∈ tailSet S X with j < ℓ, tailFactor δ (S.p j)) / ((S.p ℓ : ℝ) - 1) ^ 2

theorem level_le_budget {X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert S.m X δ c T) (ℓ : Fin S.n) :
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

/-- Step 7: the budgets sum to less than `1`. -/
theorem sum_budget_lt {X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert S.m X δ c T) :
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
      T * (100 / (189 * (X : ℝ))) := by
    simp_rw [mul_div_assoc]
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hc.T_nonneg
    exact Tail.tail_bound_family_nu X hc.two_pow_le (tailSet S X) S.p
      (S.p_strictMono.strictMonoOn _)
      (fun i hi => ⟨S.p_prime i, not_le.1 (mem_filter.1 hi).2⟩)
      (fun j => tilt δ (S.p j))
      (fun i _ => (tilt_mem hc.delta_nonneg hc.delta_le_half (S.p_prime i)).1)
      (fun i _ => tilt_le_two (hc.delta_le_half _ (S.p_prime i)))
  linarith [hc.total_lt]

/-- **The chain**: a certificate for `S.m` leaves an integer uncovered. -/
theorem uncovered_of_cert {X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert S.m X δ c T) :
    ∃ x : ℤ, ∀ i, ¬ ((S.d i : ℤ) ∣ x - S.a i) := by
  have hL0 : ∀ ℓ, 0 ≤ δL S δ ℓ := fun ℓ => hc.delta_nonneg _ (S.p_prime ℓ)
  have hL1 : ∀ ℓ, δL S δ ℓ < 1 := fun ℓ =>
    (hc.delta_le_half _ (S.p_prime ℓ)).trans_lt (by norm_num)
  obtain ⟨y, hy⟩ := Distortion.criterion_kernel (B := S.B) (δ := δL S δ) S.B_congr hL0 hL1
    (fun ℓ x => max 0 (∑ i, (if ∀ j, x j ∈ S.rect ℓ i j then S.wt ℓ i else 0) - δL S δ ℓ) /
      (1 - δL S δ ℓ))
    (fun ℓ x => S.hinge_alpha_le ℓ x le_rfl (hL1 ℓ))
    (lt_of_le_of_lt (sum_le_sum fun ℓ _ => level_le_budget S hc ℓ) (sum_budget_lt S hc))
  exact S.exists_int_of_forall_not_mem_B y hy

end Levels

/-- **Main theorem, certificate form.** If `Cert m X δ c T` holds (`2 ≤ m`), no system of
congruences with distinct moduli `≥ m` covers `ℤ`. -/
theorem not_covers_of_cert {m X : ℕ} {δ c : ℕ → ℝ} {T : ℝ} (hc : Cert m X δ c T) (hm : 2 ≤ m)
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ) (hd : Function.Injective d)
    (hdm : ∀ i, m ≤ d i) : ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) :=
  uncovered_of_cert (⟨m, d, a, hm, hd, hdm⟩ : Arith.Setup ι) hc

end MinModulus.Main

namespace MinModulus

/-- **Theorem.** Congruences `a i (mod d i)` with distinct moduli `d i ≥ 16000` do not cover `ℤ`.
Hence every covering system with distinct moduli has least modulus at most `15999`. -/
theorem not_covers {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : Function.Injective d) (hm : ∀ i, 16000 ≤ d i) :
    ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) := by
  obtain ⟨δ, c, T, hc⟩ := Main.Stub.cert_16000
  exact Main.not_covers_of_cert hc (by norm_num) d a hd hm

end MinModulus
