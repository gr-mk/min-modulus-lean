import MinModulus.Smooth.Law
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Module 4 (`Smooth`), part 2: configurations, weights, expectations

* `box Ps γ : Finset (ℕ → ℕ)` : exponent vectors `v` with `v q ≤ γ q` for `q ∈ Ps`, `v q = 0` otherwise
  (`mem_box`).  It is the image of `Finset.pi` under extension by zero (an explicit `Finset.map`,
  no classical choice).
* `weight Ps ν γ v = Π_{q ∈ Ps} ρ(q, ν q, γ q, v q)` (the product law `π`).
* `smooth Ps v = Π_{q ∈ Ps} q ^ v q` (the smooth number `s(v)`).
* `expect Ps ν γ f = Σ_{v ∈ box Ps γ} weight Ps ν γ v * f v` (the expectation `E_γ[f]`).

Main results:
* `expect_empty`, `expect_insert` : the recursive decomposition
  `E_{insert q Ps}[f] = Σ_{a ≤ γ q} ρ(q, ν q, γ q, a) · E_{Ps}[v ↦ f (update v q a)]` for `q ∉ Ps`;
* (i)   `sum_weight`, `expect_const`, `weight_nonneg`;
* (ii)  `expect_mono_cap` : `γ ≤ γ'` on `Ps`, `f` monotone ⟹ `E_γ[f] ≤ E_γ'[f]`;
* (iii) `expect_prod` : `E[Π_q h q (v q)] = Π_q E_q[h q]`;
* Fubini over disjoint blocks of primes `expect_union`, marginalization `expect_eq_of_subset`,
  parameter congruence `expect_congr_param`, and the reindexing `sum_piFinset_eq_expect`
  (a product law indexed by an arbitrary `Fintype ι` injected into `ℕ`).
-/

namespace MinModulus.Smooth

open Finset

/-- Extension by zero of a function defined on the members of `Ps`. -/
def extendZero (Ps : Finset ℕ) (f : ∀ q ∈ Ps, ℕ) : ℕ → ℕ :=
  fun q => if h : q ∈ Ps then f q h else 0

theorem extendZero_injective (Ps : Finset ℕ) : Function.Injective (extendZero Ps) := by
  intro f g hfg
  funext q h
  have := congrFun hfg q
  simpa [extendZero, h] using this

/-- Configurations: exponent vectors `v : ℕ → ℕ` with `v q ≤ γ q` for `q ∈ Ps` and `v q = 0`
for `q ∉ Ps`. -/
def box (Ps : Finset ℕ) (γ : ℕ → ℕ) : Finset (ℕ → ℕ) :=
  (Ps.pi fun q => range (γ q + 1)).map ⟨extendZero Ps, extendZero_injective Ps⟩

/-- The weight `π(v) = Π_{q ∈ Ps} ρ(q, ν q, γ q, v q)`. -/
noncomputable def weight (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (v : ℕ → ℕ) : ℝ :=
  ∏ q ∈ Ps, rho q (ν q) (γ q) (v q)

/-- The smooth number `s(v) = Π_{q ∈ Ps} q ^ v q`. -/
def smooth (Ps : Finset ℕ) (v : ℕ → ℕ) : ℕ :=
  ∏ q ∈ Ps, q ^ v q

/-- The expectation `E_γ[f] = Σ_{v ∈ box Ps γ} π(v) f(v)` under the capped tilted product law. -/
noncomputable def expect (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (f : (ℕ → ℕ) → ℝ) : ℝ :=
  ∑ v ∈ box Ps γ, weight Ps ν γ v * f v

variable {Ps : Finset ℕ} {ν : ℕ → ℝ} {γ : ℕ → ℕ}

/-! ### The box -/

theorem mem_box {v : ℕ → ℕ} :
    v ∈ box Ps γ ↔ (∀ q ∈ Ps, v q ≤ γ q) ∧ ∀ q, q ∉ Ps → v q = 0 := by
  constructor
  · intro hv
    obtain ⟨f, hf, rfl⟩ := mem_map.1 hv
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · have := mem_pi.1 hf q hq
      simp only [Function.Embedding.coeFn_mk, extendZero, hq, dite_true]
      exact Nat.lt_succ_iff.1 (mem_range.1 this)
    · simp [extendZero, hq]
  · rintro ⟨h1, h2⟩
    refine mem_map.2 ⟨fun q _ => v q,
      mem_pi.2 fun q hq => mem_range.2 (Nat.lt_succ_of_le (h1 q hq)), ?_⟩
    funext q
    by_cases hq : q ∈ Ps
    · simp [extendZero, hq]
    · simp [extendZero, hq, h2 q hq]

theorem zero_mem_box (Ps : Finset ℕ) (γ : ℕ → ℕ) : (0 : ℕ → ℕ) ∈ box Ps γ :=
  mem_box.2 ⟨fun _ _ => Nat.zero_le _, fun _ _ => rfl⟩

theorem box_empty (γ : ℕ → ℕ) : box ∅ γ = {0} := by
  ext v
  rw [mem_box, mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    funext q
    exact h q (by simp)
  · rintro rfl
    exact ⟨by simp, fun _ _ => rfl⟩

theorem box_congr {γ' : ℕ → ℕ} (h : ∀ q ∈ Ps, γ q = γ' q) : box Ps γ = box Ps γ' := by
  ext v
  simp only [mem_box]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun q hq => h q hq ▸ h1 q hq, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun q hq => (h q hq).symm ▸ h1 q hq, h2⟩

/-! ### Basic properties of `weight` and `expect` -/

/-- (i) The weights are nonnegative. -/
theorem weight_nonneg (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ) (v : ℕ → ℕ) :
    0 ≤ weight Ps ν γ v :=
  prod_nonneg fun q hq => rho_nonneg (hν q hq).1 (hν q hq).2 _ _

@[simp] theorem expect_empty (ν : ℕ → ℝ) (γ : ℕ → ℕ) (f : (ℕ → ℕ) → ℝ) :
    expect ∅ ν γ f = f 0 := by
  simp [expect, box_empty, weight]

theorem expect_congr_fun {f g : (ℕ → ℕ) → ℝ} (h : ∀ v ∈ box Ps γ, f v = g v) :
    expect Ps ν γ f = expect Ps ν γ g :=
  sum_congr rfl fun v hv => by rw [h v hv]

/-- `E` depends on `ν` and `γ` only through their values on `Ps`. -/
theorem expect_congr_param {ν' : ℕ → ℝ} {γ' : ℕ → ℕ} (hν : ∀ q ∈ Ps, ν q = ν' q)
    (hγ : ∀ q ∈ Ps, γ q = γ' q) (f : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ f = expect Ps ν' γ' f := by
  unfold expect
  rw [box_congr hγ]
  refine sum_congr rfl fun v _ => ?_
  congr 1
  exact prod_congr rfl fun q hq => by rw [hν q hq, hγ q hq]

theorem expect_add (f g : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ (fun v => f v + g v) = expect Ps ν γ f + expect Ps ν γ g := by
  simp [expect, mul_add, sum_add_distrib]

theorem expect_sub (f g : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ (fun v => f v - g v) = expect Ps ν γ f - expect Ps ν γ g := by
  simp [expect, mul_sub, sum_sub_distrib]

theorem expect_const_mul (c : ℝ) (f : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ (fun v => c * f v) = c * expect Ps ν γ f := by
  simp [expect, mul_sum, mul_left_comm]

theorem expect_mul_const (c : ℝ) (f : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ (fun v => f v * c) = expect Ps ν γ f * c := by
  simp [expect, sum_mul, mul_assoc]

theorem expect_sum {ι : Type*} (s : Finset ι) (F : ι → (ℕ → ℕ) → ℝ) :
    expect Ps ν γ (fun v => ∑ i ∈ s, F i v) = ∑ i ∈ s, expect Ps ν γ (F i) := by
  simp only [expect, mul_sum]
  exact sum_comm

theorem expect_mono (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) {f g : (ℕ → ℕ) → ℝ}
    (h : ∀ v ∈ box Ps γ, f v ≤ g v) : expect Ps ν γ f ≤ expect Ps ν γ g :=
  sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (h v hv) (weight_nonneg hν γ v)

theorem expect_nonneg (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) {f : (ℕ → ℕ) → ℝ}
    (h : ∀ v ∈ box Ps γ, 0 ≤ f v) : 0 ≤ expect Ps ν γ f :=
  sum_nonneg fun v hv => mul_nonneg (weight_nonneg hν γ v) (h v hv)

/-! ### The recursive decomposition -/

theorem update_mem_box_insert {q : ℕ} (hq : q ∉ Ps) {w : ℕ → ℕ} (hw : w ∈ box Ps γ) {a : ℕ}
    (ha : a ≤ γ q) : Function.update w q a ∈ box (insert q Ps) γ := by
  rw [mem_box] at hw ⊢
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rcases mem_insert.1 hr with rfl | hr'
    · simpa using ha
    · have : r ≠ q := fun h => hq (h ▸ hr')
      rw [Function.update_of_ne this]
      exact hw.1 r hr'
  · have h1 : r ≠ q := fun h => hr (h ▸ mem_insert_self _ _)
    have h2 : r ∉ Ps := fun h => hr (mem_insert_of_mem h)
    rw [Function.update_of_ne h1]
    exact hw.2 r h2

theorem weight_update_of_notMem {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (w : ℕ → ℕ)
    (a : ℕ) : weight Ps ν γ (Function.update w q a) = weight Ps ν γ w := by
  refine prod_congr rfl fun r hr => ?_
  have : r ≠ q := fun h => hq (h ▸ hr)
  rw [Function.update_of_ne this]

/-- **Recursive decomposition** over the set of primes: for `q ∉ Ps`,
`E_{insert q Ps}[f] = Σ_{a ≤ γ q} ρ(q, ν q, γ q, a) · E_{Ps}[v ↦ f (update v q a)]`.
(The right side is `expect1 q (ν q) (γ q) (fun a => expect Ps ν γ (fun v => f (update v q a)))`.) -/
theorem expect_insert {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (f : (ℕ → ℕ) → ℝ) :
    expect (insert q Ps) ν γ f =
      ∑ a ∈ range (γ q + 1),
        rho q (ν q) (γ q) a * expect Ps ν γ (fun v => f (Function.update v q a)) := by
  simp only [expect, mul_sum]
  rw [← sum_product' (range (γ q + 1)) (box Ps γ)
    (fun a w => rho q (ν q) (γ q) a * (weight Ps ν γ w * f (Function.update w q a)))]
  symm
  refine sum_nbij' (fun x => Function.update x.2 q x.1) (fun v => (v q, Function.update v q 0))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, w⟩ h
    rw [mem_product] at h
    exact update_mem_box_insert hq h.2 (Nat.lt_succ_iff.1 (mem_range.1 h.1))
  · intro v hv
    rw [mem_box] at hv
    rw [mem_product, mem_box]
    refine ⟨mem_range.2 (Nat.lt_succ_of_le (hv.1 q (mem_insert_self q Ps))),
      fun r hr => ?_, fun r hr => ?_⟩
    · dsimp only
      have : r ≠ q := fun h => hq (h ▸ hr)
      rw [Function.update_of_ne this]
      exact hv.1 r (mem_insert_of_mem hr)
    · dsimp only
      by_cases hrq : r = q
      · subst hrq; simp
      · rw [Function.update_of_ne hrq]
        exact hv.2 r (by simp [hrq, hr])
  · rintro ⟨a, w⟩ h
    rw [mem_product, mem_box] at h
    have hwq : w q = 0 := h.2.2 q hq
    simp only [Function.update_self, Function.update_idem, Prod.mk.injEq, true_and]
    funext r
    by_cases hrq : r = q
    · subst hrq; simp [hwq]
    · simp [Function.update_of_ne hrq]
  · intro v _
    simp
  · rintro ⟨a, w⟩ _
    simp only [weight]
    rw [prod_insert hq, Function.update_self]
    have := weight_update_of_notMem hq ν γ w a
    simp only [weight] at this
    rw [this]
    ring

/-- The recursive decomposition written with the one-coordinate expectation `expect1`. -/
theorem expect_insert' {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (f : (ℕ → ℕ) → ℝ) :
    expect (insert q Ps) ν γ f =
      expect1 q (ν q) (γ q) (fun a => expect Ps ν γ (fun v => f (Function.update v q a))) :=
  expect_insert hq ν γ f

/-- The recursive decomposition in the form `Ps ∪ {q}`. -/
theorem expect_union_singleton {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ)
    (f : (ℕ → ℕ) → ℝ) :
    expect (Ps ∪ {q}) ν γ f =
      ∑ a ∈ range (γ q + 1),
        rho q (ν q) (γ q) a * expect Ps ν γ (fun v => f (Function.update v q a)) := by
  rw [union_comm, ← insert_eq]
  exact expect_insert hq ν γ f

/-- A single prime: `E_{{q}}[f] = Σ_{a ≤ γ q} ρ(a) f(update 0 q a)`. -/
theorem expect_singleton (q : ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (f : (ℕ → ℕ) → ℝ) :
    expect {q} ν γ f = expect1 q (ν q) (γ q) (fun a => f (Function.update 0 q a)) := by
  rw [← insert_empty_eq q, expect_insert (notMem_empty q)]
  simp [expect1]

/-- (i) Normalization: `E[1] = 1`. -/
theorem expect_one (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) : expect Ps ν γ (fun _ => 1) = 1 := by
  induction Ps using Finset.induction_on with
  | empty => simp
  | insert q Ps hq ih =>
    rw [expect_insert hq]
    simp only [ih, mul_one]
    exact sum_rho q (ν q) (γ q)

/-- (i) Normalization: `Σ_v π(v) = 1`. -/
theorem sum_weight (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) :
    ∑ v ∈ box Ps γ, weight Ps ν γ v = 1 := by
  simpa [expect] using expect_one Ps ν γ

theorem expect_const (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (c : ℝ) :
    expect Ps ν γ (fun _ => c) = c := by
  have := expect_const_mul (Ps := Ps) (ν := ν) (γ := γ) c (fun _ => 1)
  simpa [expect_one] using this

/-- (iii) **Independence / product formula**: `E[Π_{q ∈ Ps} h q (v q)] = Π_{q ∈ Ps} E_q[h q]`. -/
theorem expect_prod (Ps : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (h : ℕ → ℕ → ℝ) :
    expect Ps ν γ (fun v => ∏ q ∈ Ps, h q (v q)) = ∏ q ∈ Ps, expect1 q (ν q) (γ q) (h q) := by
  induction Ps using Finset.induction_on with
  | empty => simp
  | insert q Ps hq ih =>
    rw [expect_insert hq, prod_insert hq]
    have key : ∀ a, expect Ps ν γ (fun v => ∏ r ∈ insert q Ps, h r (Function.update v q a r)) =
        h q a * ∏ r ∈ Ps, expect1 r (ν r) (γ r) (h r) := by
      intro a
      rw [← ih, ← expect_const_mul]
      refine expect_congr_fun fun v _ => ?_
      rw [prod_insert hq, Function.update_self]
      congr 1
      refine prod_congr rfl fun r hr => ?_
      have hrq : r ≠ q := fun h => hq (h ▸ hr)
      rw [Function.update_of_ne hrq]
    simp_rw [key]
    simp only [expect1, sum_mul, mul_assoc]

/-- (ii) **Monotone coupling in the caps**: if `γ ≤ γ'` on `Ps` and `f` is nondecreasing
(coordinatewise), then `E_γ[f] ≤ E_γ'[f]`. -/
theorem expect_mono_cap (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) {γ γ' : ℕ → ℕ}
    (hγ : ∀ q ∈ Ps, γ q ≤ γ' q) {f : (ℕ → ℕ) → ℝ} (hf : Monotone f) :
    expect Ps ν γ f ≤ expect Ps ν γ' f := by
  induction Ps using Finset.induction_on generalizing f with
  | empty => simp
  | insert q Ps hq ih =>
    have hν' : ∀ r ∈ Ps, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
    have hγ' : ∀ r ∈ Ps, γ r ≤ γ' r := fun r hr => hγ r (mem_insert_of_mem hr)
    have hνq := hν q (mem_insert_self q Ps)
    have hmono : ∀ a, Monotone (fun v => f (Function.update v q a)) := fun a v w hvw =>
      hf (update_le_update_iff.2 ⟨le_rfl, fun j _ => hvw j⟩)
    rw [expect_insert hq, expect_insert hq]
    have hG : Monotone (fun a => expect Ps ν γ' (fun v => f (Function.update v q a))) :=
      fun a b hab => expect_mono hν' fun v _ =>
        hf (update_le_update_iff.2 ⟨hab, fun _ _ => le_rfl⟩)
    calc ∑ a ∈ range (γ q + 1),
          rho q (ν q) (γ q) a * expect Ps ν γ (fun v => f (Function.update v q a))
        ≤ ∑ a ∈ range (γ q + 1),
          rho q (ν q) (γ q) a * expect Ps ν γ' (fun v => f (Function.update v q a)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih hν' hγ' (hmono a))
            (rho_nonneg hνq.1 hνq.2 _ _)
      _ ≤ ∑ a ∈ range (γ' q + 1),
          rho q (ν q) (γ' q) a * expect Ps ν γ' (fun v => f (Function.update v q a)) :=
          expect1_mono_cap hνq.1 hG (hγ q (mem_insert_self q Ps))

/-- **Monotonicity in the tilts**: for nondecreasing `f` and `ν ≤ ν'` on `Ps` (both admissible),
`E_ν[f] ≤ E_ν'[f]`.  (So upper bounds on `ν_q = 1/(1-δ_q)` may be used.) -/
theorem expect_mono_tilt {ν ν' : ℕ → ℝ} (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q)
    (hν' : ∀ q ∈ Ps, 0 ≤ ν' q ∧ ν' q ≤ q) (h : ∀ q ∈ Ps, ν q ≤ ν' q) (γ : ℕ → ℕ)
    {f : (ℕ → ℕ) → ℝ} (hf : Monotone f) :
    expect Ps ν γ f ≤ expect Ps ν' γ f := by
  induction Ps using Finset.induction_on generalizing f with
  | empty => simp
  | insert q Ps hq ih =>
    have hν₁ : ∀ r ∈ Ps, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
    have hν₁' : ∀ r ∈ Ps, 0 ≤ ν' r ∧ ν' r ≤ r := fun r hr => hν' r (mem_insert_of_mem hr)
    have h₁ : ∀ r ∈ Ps, ν r ≤ ν' r := fun r hr => h r (mem_insert_of_mem hr)
    have hνq := hν q (mem_insert_self q Ps)
    have hmono : ∀ a, Monotone (fun v => f (Function.update v q a)) := fun a v w hvw =>
      hf (update_le_update_iff.2 ⟨le_rfl, fun j _ => hvw j⟩)
    rw [expect_insert hq, expect_insert hq]
    have hG : Monotone (fun a => expect Ps ν' γ (fun v => f (Function.update v q a))) :=
      fun a b hab => expect_mono hν₁' fun v _ =>
        hf (update_le_update_iff.2 ⟨hab, fun _ _ => le_rfl⟩)
    calc ∑ a ∈ range (γ q + 1),
          rho q (ν q) (γ q) a * expect Ps ν γ (fun v => f (Function.update v q a))
        ≤ ∑ a ∈ range (γ q + 1),
          rho q (ν q) (γ q) a * expect Ps ν' γ (fun v => f (Function.update v q a)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (ih hν₁ hν₁' h₁ (hmono a))
            (rho_nonneg hνq.1 hνq.2 _ _)
      _ ≤ ∑ a ∈ range (γ q + 1),
          rho q (ν' q) (γ q) a * expect Ps ν' γ (fun v => f (Function.update v q a)) :=
          expect1_mono_tilt (h q (mem_insert_self q Ps)) hG q (γ q)

/-- **Exact coupling** in the caps: for `γ ≤ γ'` on `Ps`, the law with caps `γ` is the image of
the law with caps `γ'` under the clipping `v ↦ (q ↦ min (v q) (γ q))`. -/
theorem expect_clip {γ γ' : ℕ → ℕ} (hγ : ∀ q ∈ Ps, γ q ≤ γ' q) (f : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ f = expect Ps ν γ' (fun v => f (fun q => min (v q) (γ q))) := by
  induction Ps using Finset.induction_on generalizing f with
  | empty =>
    simp only [expect_empty]
    congr 1
  | insert q Ps hq ih =>
    have hγ' : ∀ r ∈ Ps, γ r ≤ γ' r := fun r hr => hγ r (mem_insert_of_mem hr)
    rw [expect_insert hq, expect_insert hq]
    have key : ∀ a' : ℕ, ∀ v : ℕ → ℕ, (fun r => min (Function.update v q a' r) (γ r)) =
        Function.update (fun r => min (v r) (γ r)) q (min a' (γ q)) := by
      intro a' v
      funext r
      by_cases hrq : r = q
      · subst hrq; simp
      · simp [Function.update_of_ne hrq]
    simp_rw [ih hγ', key]
    exact expect1_clip (hγ q (mem_insert_self q Ps))
      (fun a => expect Ps ν γ' (fun v => f (Function.update (fun r => min (v r) (γ r)) q a)))

/-- **Caps may be taken as large as desired** (monotone `f`): if `E_{γ'}[f] ≤ B` for every
`γ' ≥ γ₀` on `Ps`, then `E_γ[f] ≤ B` for every `γ`. -/
theorem expect_le_of_forall_ge_cap (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q) {f : (ℕ → ℕ) → ℝ}
    (hf : Monotone f) (γ₀ : ℕ → ℕ) {B : ℝ}
    (hB : ∀ γ' : ℕ → ℕ, (∀ q ∈ Ps, γ₀ q ≤ γ' q) → expect Ps ν γ' f ≤ B) (γ : ℕ → ℕ) :
    expect Ps ν γ f ≤ B :=
  (expect_mono_cap hν (γ' := fun q => max (γ q) (γ₀ q)) (fun _ _ => le_max_left _ _) hf).trans
    (hB _ fun _ _ => le_max_right _ _)

/-! ### Fubini over disjoint blocks, marginalization -/

/-- **Fubini** over two disjoint blocks of primes: configurations on `A ∪ B` are sums `v + w` of
configurations on `A` and on `B`. -/
theorem expect_union {A B : Finset ℕ} (hAB : Disjoint A B) (ν : ℕ → ℝ) (γ : ℕ → ℕ)
    (f : (ℕ → ℕ) → ℝ) :
    expect (A ∪ B) ν γ f = expect A ν γ (fun v => expect B ν γ (fun w => f (v + w))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp
  | insert q A hq ih =>
    rw [disjoint_insert_left] at hAB
    have hqAB : q ∉ A ∪ B := by simp [hq, hAB.1]
    rw [insert_union, expect_insert hqAB, expect_insert hq]
    refine sum_congr rfl fun a _ => ?_
    rw [ih hAB.2]
    congr 1
    congr 1
    funext v
    refine expect_congr_fun fun w hw => ?_
    have hwq : w q = 0 := (mem_box.1 hw).2 q hAB.1
    congr 1
    funext r
    by_cases hrq : r = q
    · subst hrq; simp [hwq]
    · simp [Function.update_of_ne hrq]

/-- **Marginalization**: if `f` depends only on the coordinates in `A ⊆ Ps`, then
`E_{Ps}[f] = E_{A}[f]`. -/
theorem expect_eq_of_subset {A : Finset ℕ} (hA : A ⊆ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ)
    {f : (ℕ → ℕ) → ℝ} (hf : ∀ v w, (∀ q ∈ A, v q = w q) → f v = f w) :
    expect Ps ν γ f = expect A ν γ f := by
  have hPs : A ∪ (Ps \ A) = Ps := union_sdiff_of_subset hA
  rw [← hPs, expect_union disjoint_sdiff]
  refine expect_congr_fun fun v _ => ?_
  have : expect (Ps \ A) ν γ (fun w => f (v + w)) = expect (Ps \ A) ν γ (fun _ => f v) := by
    refine expect_congr_fun fun w hw => hf _ _ fun q hq => ?_
    have : w q = 0 := (mem_box.1 hw).2 q (fun h => (mem_sdiff.1 h).2 hq)
    simp [this]
  rw [this, expect_const]

/-- If `f` does not depend on the coordinate `q ∉ Ps`, adding `q` does not change `E[f]`. -/
theorem expect_insert_of_indep {q : ℕ} (hq : q ∉ Ps) (ν : ℕ → ℝ) (γ : ℕ → ℕ)
    {f : (ℕ → ℕ) → ℝ} (hf : ∀ v a, f (Function.update v q a) = f v) :
    expect (insert q Ps) ν γ f = expect Ps ν γ f := by
  rw [expect_insert hq]
  simp only [hf, ← sum_mul, sum_rho, one_mul]

/-- With all caps `0`, the law is the point mass at `v = 0`. -/
theorem expect_of_cap_zero (hγ : ∀ q ∈ Ps, γ q = 0) (f : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ f = f 0 := by
  have hbox : box Ps γ = {0} := by
    ext v
    rw [mem_box, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      funext q
      by_cases hq : q ∈ Ps
      · have := h1 q hq
        rw [hγ q hq] at this
        exact Nat.le_zero.1 this
      · exact h2 q hq
    · rintro rfl
      exact ⟨fun q _ => Nat.zero_le _, fun _ _ => rfl⟩
  rw [expect, hbox, sum_singleton, weight, prod_eq_one (fun q hq => by simp [hγ q hq]), one_mul]

/-- Primes with cap `0` can be added or removed freely: if `A ⊆ Ps` and `γ = 0` on `Ps \ A`,
then `E_{Ps}[f] = E_{A}[f]` (no assumption on `f`). -/
theorem expect_eq_of_cap_zero_off {A : Finset ℕ} (hA : A ⊆ Ps)
    (hγ : ∀ q ∈ Ps, q ∉ A → γ q = 0) (f : (ℕ → ℕ) → ℝ) :
    expect Ps ν γ f = expect A ν γ f := by
  rw [← union_sdiff_of_subset hA, expect_union disjoint_sdiff]
  refine expect_congr_fun fun v _ => ?_
  rw [expect_of_cap_zero (fun q hq => hγ q (mem_sdiff.1 hq).1 (mem_sdiff.1 hq).2), add_zero]

/-- **Enlarging the set of primes and the caps** (monotone `f`): for `A ⊆ Ps` and `γ ≤ γ'` on `A`,
`E_{A,γ}[f] ≤ E_{Ps,γ'}[f]` (whatever `γ'` is on `Ps \ A`). -/
theorem expect_le_of_subset {A : Finset ℕ} (hA : A ⊆ Ps) (hν : ∀ q ∈ Ps, 0 ≤ ν q ∧ ν q ≤ q)
    {γ γ' : ℕ → ℕ} (hγ : ∀ q ∈ A, γ q ≤ γ' q) {f : (ℕ → ℕ) → ℝ} (hf : Monotone f) :
    expect A ν γ f ≤ expect Ps ν γ' f := by
  classical
  let γ'' : ℕ → ℕ := fun q => if q ∈ A then γ q else 0
  have h1 : expect A ν γ f = expect A ν γ'' f :=
    expect_congr_param (fun _ _ => rfl) (fun q hq => by simp [γ'', hq]) f
  have h2 : expect Ps ν γ'' f = expect A ν γ'' f :=
    expect_eq_of_cap_zero_off hA (fun q _ hqA => by simp [γ'', hqA]) f
  rw [h1, ← h2]
  refine expect_mono_cap hν (fun q _ => ?_) hf
  by_cases hqA : q ∈ A
  · simp only [γ'', hqA, ↓reduceIte]
    exact hγ q hqA
  · simp [γ'', hqA]

/-! ### Reindexing by an arbitrary finite index type -/

/-- A product law indexed by a `Fintype ι`, transported to the primes along an injection
`e : ι → ℕ`, is the law `expect (univ.image e) ν γ`. -/
theorem sum_piFinset_eq_expect {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (he : Function.Injective e) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (F : (ι → ℕ) → ℝ) :
    ∑ V ∈ Fintype.piFinset (fun i => range (γ (e i) + 1)),
        (∏ i, rho (e i) (ν (e i)) (γ (e i)) (V i)) * F V =
      expect (univ.image e) ν γ (fun v => F (fun i => v (e i))) := by
  unfold expect
  refine sum_nbij' (fun V => Function.extend e V 0) (fun v i => v (e i)) ?_ ?_ ?_ ?_ ?_
  · intro V hV
    rw [Fintype.mem_piFinset] at hV
    rw [mem_box]
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hq
      rw [he.extend_apply]
      exact Nat.lt_succ_iff.1 (mem_range.1 (hV i))
    · rw [Function.extend_apply']
      · rfl
      · rintro ⟨i, rfl⟩
        exact hq (mem_image_of_mem e (mem_univ i))
  · intro v hv
    rw [mem_box] at hv
    rw [Fintype.mem_piFinset]
    intro i
    exact mem_range.2 (Nat.lt_succ_of_le (hv.1 (e i) (mem_image_of_mem e (mem_univ i))))
  · intro V _
    funext i
    exact he.extend_apply V 0 i
  · intro v hv
    rw [mem_box] at hv
    funext q
    by_cases hq : ∃ i, e i = q
    · obtain ⟨i, rfl⟩ := hq
      exact he.extend_apply (fun i => v (e i)) 0 i
    · rw [Function.extend_apply' _ _ _ hq]
      refine (hv.2 q fun hmem => hq ?_).symm
      obtain ⟨i, -, hi⟩ := mem_image.1 hmem
      exact ⟨i, hi⟩
  · intro V _
    simp only [weight]
    rw [prod_image fun i _ j _ hij => he hij]
    simp only [he.extend_apply]

/-- `Fin`-valued version of `sum_piFinset_eq_expect`: a product law on
`(i : ι) → Fin (γ (e i) + 1)` transported along an injection `e : ι → ℕ`. -/
theorem sum_pi_fin_eq_expect {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (he : Function.Injective e) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (F : (ι → ℕ) → ℝ) :
    ∑ V : (i : ι) → Fin (γ (e i) + 1),
        (∏ i, rho (e i) (ν (e i)) (γ (e i)) (V i)) * F (fun i => (V i : ℕ)) =
      expect (univ.image e) ν γ (fun v => F (fun i => v (e i))) := by
  rw [← sum_piFinset_eq_expect e he ν γ F]
  refine sum_nbij' (fun V i => (V i : ℕ))
    (fun W i => ⟨min (W i) (γ (e i)), Nat.lt_succ_of_le (min_le_right _ _)⟩) ?_ ?_ ?_ ?_ ?_
  · intro V _
    rw [Fintype.mem_piFinset]
    exact fun i => mem_range.2 (V i).is_lt
  · intro W _
    exact mem_univ _
  · intro V _
    funext i
    exact Fin.ext (min_eq_left (Nat.lt_succ_iff.1 (V i).is_lt))
  · intro W hW
    rw [Fintype.mem_piFinset] at hW
    funext i
    exact min_eq_left (Nat.lt_succ_iff.1 (mem_range.1 (hW i)))
  · intro V _
    rfl

/-! ### The smooth number `s(v)` -/

@[simp] theorem smooth_empty (v : ℕ → ℕ) : smooth ∅ v = 1 := by simp [smooth]

theorem smooth_insert {q : ℕ} (hq : q ∉ Ps) (v : ℕ → ℕ) :
    smooth (insert q Ps) v = q ^ v q * smooth Ps v :=
  prod_insert hq

theorem smooth_update_of_notMem {q : ℕ} (hq : q ∉ Ps) (v : ℕ → ℕ) (a : ℕ) :
    smooth Ps (Function.update v q a) = smooth Ps v := by
  refine prod_congr rfl fun r hr => ?_
  have : r ≠ q := fun h => hq (h ▸ hr)
  rw [Function.update_of_ne this]

@[simp] theorem smooth_zero (Ps : Finset ℕ) : smooth Ps 0 = 1 := by simp [smooth]

theorem smooth_pos (hPs : ∀ q ∈ Ps, 0 < q) (v : ℕ → ℕ) : 0 < smooth Ps v :=
  prod_pos fun q hq => pow_pos (hPs q hq) _

theorem smooth_ne_zero (hPs : ∀ q ∈ Ps, 0 < q) (v : ℕ → ℕ) : smooth Ps v ≠ 0 :=
  (smooth_pos hPs v).ne'

/-- `s(v) ∣ s(w)` when `v ≤ w` on `Ps`. -/
theorem smooth_dvd_smooth {v w : ℕ → ℕ} (h : ∀ q ∈ Ps, v q ≤ w q) : smooth Ps v ∣ smooth Ps w :=
  prod_dvd_prod_of_dvd _ _ fun q hq => pow_dvd_pow q (h q hq)

/-- For configurations on disjoint blocks, `s_{A ∪ B}(v + w) = s_A(v) · s_B(w)`. -/
theorem smooth_union_add {A B : Finset ℕ} (hAB : Disjoint A B) {v w : ℕ → ℕ}
    (hv : ∀ q ∈ B, v q = 0) (hw : ∀ q ∈ A, w q = 0) :
    smooth (A ∪ B) (v + w) = smooth A v * smooth B w := by
  unfold smooth
  rw [prod_union hAB]
  congr 1
  · exact prod_congr rfl fun q hq => by simp [hw q hq]
  · exact prod_congr rfl fun q hq => by simp [hv q hq]

end MinModulus.Smooth
