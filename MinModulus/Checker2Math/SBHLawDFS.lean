import MinModulus.Checker2Math.SBHLaw

/-!
# `Checker2Math.SBHLawDFS`: the DFS over `S`, pruning bounds, and `hingeLoss` in leaf form (L2-A)

STATUS: complete (fully proved; lean2 stage 2, agent L2-A). Every theorem depends only on
`propext`, `Classical.choice`, `Quot.sound`.

## The DFS model (`SBH.dfsNode`/`dfsExp`)
The primes of `S` are `qf 0, …, qf (n−1)` (injective on `[0, n)`; the code: `qf j = Sq[j]!`,
increasing). The DFS at depth `j` has fixed the exponents of `qf 0, …, qf (j−1)` (a prefix
assignment `u`, zero on `qf j, …`). For a leaf function `G` (a function of the full exponent
vector of `S`):
* `nodeVal qf n ν γ G j u = E_{sufSet j}[G(u + ·)]` (`sufSet j = {qf j, …, qf (n−1)}`),
* `expVal qf n ν γ G j a u = Σ_{a ≤ x ≤ γ(qf j)} ρ_{qf j}(x)·nodeVal (j+1) (u[qf j ↦ x])`
  (the subtree `{v_{qf j} ≥ a}`).
Recursions: `nodeVal_zero` (the root is `E_S[G]`), `nodeVal_of_le` (a leaf is `G u`),
`nodeVal_eq_expVal` (`dfsNode → dfsExp … 0`), `expVal_eq` (`dfsExp` at `a`: the child `v = a`
plus the siblings `≥ a+1`), `expVal_of_gt`, nonnegativity (`nodeVal_nonneg`, `expVal_nonneg`), and
the **pruning bound** `expVal_le`: if `0 ≤ G ≤ C·τ_S`, then
`expVal j a u ≤ τ_S(u)·h_γ(a)·(C·∏_{q ∈ sufSet (j+1)}(1 + ν_q/(q − 1)))`, `h_γ(a) = E[(v+1)1{v ≥ a}]`
(`TauLaw.hMass`), with `hMass_le` (`h_γ(0) ≤ 1 + ν/(q−1)`, `h_γ(A) ≤ ν q^{−A}(A + 1 + 1/(q−1))`:
the two branches of the code's `hUp`) and `hMass_nonneg`. The generic form is
`sum_tail_expect_le`; helpers `sufSet_of_le`, `sufSet_eq_insert`, `mem_sufSet`,
`qf_notMem_sufSet`, `tauN_sufSet`, `add_update_comm`, `nu_mem_sufSet`, `tauN_add_update`.

Suggested use (L2-D): by induction on the fuel of `dfsNode`/`dfsExp`, with `τ = tauN S u` and `pat`
the small pattern of `u`, show `wv(acc'.leaf + acc'.prune) ≥ wv(acc.leaf + acc.prune) + pv P·nodeVal j u`
(resp. `+ pv P·expVal j a u`): a leaf uses `nodeVal_of_le` and `SBHLaw.sbhLeaf_le`; a pruned subtree
uses `expVal_le`; a recursion step uses `expVal_eq` and `pv(mulUp P pm[a]) ≥ pv P·ρ(a)`.

## `hingeLoss` in leaf form
`hingeLoss_eq_sbhLeaf`: `hingeLoss m δ p γ = E_S[G]/((p−1)(1−δ_p))` with the leaf function
`G(u) = sbhLeaf (B ∪ H) ν γ (sbhProfile p m B (s_S(u))) τ_S(u) (F(s_S(u)) + δ_p(p−1)) (1 − 1/p)`
(Fubini over `S` and `B ∪ H` after `Checker2Math.hingeLoss_eq_sbh`); `bstat_sbhProfile` (the `b`
of the S/B/H identity), `cc_nonneg`, `Fsum_nonneg` (so the thresholds of `G` are `≥ 0` when
`δ_p ≥ 0`, and `SBHLaw.sbhLeaf_le_prod` gives `0 ≤ G ≤ τ_S·∏_{B∪H}(1 + ν/(q−1))` for `expVal_le`).
-/

namespace MinModulus.Checker2Math.A

open Finset MinModulus.Smooth MinModulus.CheckerMath MinModulus.Checker2Math

/-! ## Pruning: the generic tail bound -/

/-- **Pruning, generic form**: for `q ∉ Ps` and `0 ≤ f(w[q ↦ x]) ≤ K·(x+1)·g(w)` on the box,
`Σ_{A ≤ x ≤ γ q} ρ_q(x)·E_Ps[f(·[q ↦ x])] ≤ K·h_γ(A)·E_Ps[g]`. -/
theorem sum_tail_expect_le {q : ℕ} {Ps : Finset ℕ} {ν : ℕ → ℝ}
    (hν : ∀ r ∈ insert q Ps, 0 ≤ ν r ∧ ν r ≤ r) (γ : ℕ → ℕ) {f g : (ℕ → ℕ) → ℝ} {K : ℝ}
    (hf : ∀ w ∈ box Ps γ, ∀ x ≤ γ q, 0 ≤ f (Function.update w q x) ∧
      f (Function.update w q x) ≤ K * ((x : ℝ) + 1) * g w) (A : ℕ) :
    ∑ x ∈ Ico A (γ q + 1), rho q (ν q) (γ q) x * expect Ps ν γ (fun w => f (Function.update w q x))
      ≤ K * hMass q (ν q) (γ q) A * expect Ps ν γ g := by
  have hνPs : ∀ r ∈ Ps, 0 ≤ ν r ∧ ν r ≤ r := fun r hr => hν r (mem_insert_of_mem hr)
  have hνq := hν q (mem_insert_self q Ps)
  have h1 : ∀ x ∈ Ico A (γ q + 1), rho q (ν q) (γ q) x *
      expect Ps ν γ (fun w => f (Function.update w q x)) ≤
      rho q (ν q) (γ q) x * (K * ((x : ℝ) + 1) * expect Ps ν γ g) := by
    intro x hx
    have hxγ : x ≤ γ q := Nat.lt_succ_iff.1 (mem_Ico.1 hx).2
    refine mul_le_mul_of_nonneg_left ?_ (rho_nonneg hνq.1 hνq.2 _ _)
    rw [← expect_const_mul]
    exact expect_mono hνPs fun w hw => (hf w hw x hxγ).2
  refine (sum_le_sum h1).trans (le_of_eq ?_)
  have e : hMass q (ν q) (γ q) A = ∑ x ∈ Ico A (γ q + 1), rho q (ν q) (γ q) x * ((x : ℝ) + 1) := by
    unfold hMass expect1
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter]
    congr 1
    ext x
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [e, mul_sum, sum_mul]
  exact sum_congr rfl fun x _ => by ring

/-- `h_γ(A) = E_γ[(v+1)·1{v ≥ A}]`, uniform bounds (the code's `hUp`): `1 + ν/(q−1)` for
`A = 0`, `ν q^{−A} (A + 1 + 1/(q−1))` for `A ≥ 1`. -/
theorem hMass_le {q : ℕ} (hq : 1 < q) {ν : ℝ} (hν : 0 ≤ ν) (γ A : ℕ) :
    hMass q ν γ A ≤
      if A = 0 then 1 + ν / ((q : ℝ) - 1)
      else ν * ((q : ℝ)⁻¹) ^ A * ((A : ℝ) + 1 + 1 / ((q : ℝ) - 1)) := by
  split_ifs with hA
  · subst hA
    have : hMass q ν γ 0 = expect1 q ν γ (fun a => (a : ℝ) + 1) := by
      unfold hMass
      simp
    rw [this]
    exact expect1_add_one_le hq hν γ
  · exact expect1_hA_le hq hν (Nat.one_le_iff_ne_zero.2 hA) γ

theorem hMass_nonneg {q : ℕ} {ν : ℝ} (hν : 0 ≤ ν) (hνq : ν ≤ q) (γ A : ℕ) :
    0 ≤ hMass q ν γ A :=
  expect1_nonneg hν hνq fun a _ => by split_ifs <;> positivity

/-! ## The DFS model -/

/-- The primes at depth `≥ j`: `{qf j, …, qf (n−1)}`. -/
def sufSet (qf : ℕ → ℕ) (n j : ℕ) : Finset ℕ := (Ico j n).image qf

/-- DFS node value at depth `j` with prefix assignment `u`: `E_{sufSet j}[G(u + ·)]`. -/
noncomputable def nodeVal (qf : ℕ → ℕ) (n : ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (G : (ℕ → ℕ) → ℝ)
    (j : ℕ) (u : ℕ → ℕ) : ℝ :=
  expect (sufSet qf n j) ν γ (fun v => G (u + v))

/-- DFS exponent-step value: the subtree `{v_{qf j} ≥ a}`,
`Σ_{a ≤ x ≤ γ(qf j)} ρ_{qf j}(x)·nodeVal (j+1) (u[qf j ↦ x])`. -/
noncomputable def expVal (qf : ℕ → ℕ) (n : ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (G : (ℕ → ℕ) → ℝ)
    (j a : ℕ) (u : ℕ → ℕ) : ℝ :=
  ∑ x ∈ Ico a (γ (qf j) + 1),
    rho (qf j) (ν (qf j)) (γ (qf j)) x * nodeVal qf n ν γ G (j + 1) (Function.update u (qf j) x)

section DFS

variable {qf : ℕ → ℕ} {n : ℕ} {ν : ℕ → ℝ} {γ : ℕ → ℕ} {G : (ℕ → ℕ) → ℝ}

theorem sufSet_of_le {j : ℕ} (h : n ≤ j) : sufSet qf n j = ∅ := by
  unfold sufSet
  rw [Ico_eq_empty_of_le h, image_empty]

theorem sufSet_eq_insert {j : ℕ} (h : j < n) :
    sufSet qf n j = insert (qf j) (sufSet qf n (j + 1)) := by
  unfold sufSet
  have : Ico j n = insert j (Ico (j + 1) n) := by
    ext i
    simp only [mem_Ico, mem_insert]
    omega
  rw [this, image_insert]

theorem mem_sufSet {j r : ℕ} : r ∈ sufSet qf n j ↔ ∃ i, (j ≤ i ∧ i < n) ∧ qf i = r := by
  unfold sufSet
  simp only [mem_image, mem_Ico]

theorem qf_notMem_sufSet (hinj : Set.InjOn qf (Set.Iio n)) {j : ℕ} (h : j < n) :
    qf j ∉ sufSet qf n (j + 1) := by
  rw [mem_sufSet]
  rintro ⟨i, ⟨hi1, hi2⟩, hqi⟩
  have := hinj (Set.mem_Iio.2 hi2) (Set.mem_Iio.2 h) hqi
  omega

/-- `τ` over `sufSet j` as a product over indices. -/
theorem tauN_sufSet (hinj : Set.InjOn qf (Set.Iio n)) (j : ℕ) (w : ℕ → ℕ) :
    tauN (sufSet qf n j) w = ∏ i ∈ Ico j n, (w (qf i) + 1) := by
  unfold tauN sufSet
  rw [prod_image]
  intro x hx y hy hxy
  exact hinj (Set.mem_Iio.2 (mem_Ico.1 (mem_coe.1 hx)).2) (Set.mem_Iio.2 (mem_Ico.1 (mem_coe.1 hy)).2) hxy

/-- The root: `nodeVal 0 0 = E_S[G]`, `S = sufSet qf n 0`. -/
theorem nodeVal_zero : nodeVal qf n ν γ G 0 0 = expect (sufSet qf n 0) ν γ G := by
  unfold nodeVal
  congr 1
  funext v
  rw [zero_add]

/-- A leaf (`j ≥ n`): `nodeVal j u = G u`. -/
theorem nodeVal_of_le {j : ℕ} (h : n ≤ j) (u : ℕ → ℕ) : nodeVal qf n ν γ G j u = G u := by
  unfold nodeVal
  rw [sufSet_of_le h, expect_empty, add_zero]

/-- `u + w[q ↦ x] = u[q ↦ x] + w` when `u q = 0 = w q`. -/
theorem add_update_comm {u w : ℕ → ℕ} {q : ℕ} (hu : u q = 0) (hw : w q = 0) (x : ℕ) :
    u + Function.update w q x = Function.update u q x + w := by
  funext r
  by_cases hr : r = q
  · subst hr
    simp [hu, hw]
  · simp [Function.update_of_ne hr]

/-- `dfsNode` at depth `j < n` is `dfsExp` at exponent `0` (`u` must vanish at `qf j`). -/
theorem nodeVal_eq_expVal (hinj : Set.InjOn qf (Set.Iio n)) {j : ℕ} (h : j < n) {u : ℕ → ℕ}
    (hu : u (qf j) = 0) : nodeVal qf n ν γ G j u = expVal qf n ν γ G j 0 u := by
  unfold nodeVal expVal
  rw [sufSet_eq_insert h, expect_insert (qf_notMem_sufSet hinj h), range_eq_Ico]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  refine expect_congr_fun fun v hv => ?_
  have hvq : v (qf j) = 0 := (mem_box.1 hv).2 _ (qf_notMem_sufSet hinj h)
  rw [add_update_comm hu hvq]

/-- `dfsExp` at exponent `a ≤ γ(qf j)`: the child `v_{qf j} = a` plus the subtree `≥ a + 1`. -/
theorem expVal_eq {j a : ℕ} (ha : a ≤ γ (qf j)) (u : ℕ → ℕ) :
    expVal qf n ν γ G j a u =
      rho (qf j) (ν (qf j)) (γ (qf j)) a * nodeVal qf n ν γ G (j + 1) (Function.update u (qf j) a)
        + expVal qf n ν γ G j (a + 1) u := by
  unfold expVal
  rw [sum_eq_sum_Ico_succ_bot (by omega)]

/-- Beyond the cap the subtree is empty. -/
theorem expVal_of_gt {j a : ℕ} (ha : γ (qf j) < a) (u : ℕ → ℕ) :
    expVal qf n ν γ G j a u = 0 := by
  unfold expVal
  rw [Ico_eq_empty_of_le (by omega), sum_empty]

/-- The tilt hypothesis on `sufSet j`. -/
theorem nu_mem_sufSet (hν : ∀ i < n, 0 ≤ ν (qf i) ∧ ν (qf i) ≤ qf i) (j : ℕ) :
    ∀ q ∈ sufSet qf n j, 0 ≤ ν q ∧ ν q ≤ q := by
  intro q hq
  obtain ⟨i, ⟨-, hi⟩, rfl⟩ := mem_sufSet.1 hq
  exact hν i hi

theorem nodeVal_nonneg (hν : ∀ i < n, 0 ≤ ν (qf i) ∧ ν (qf i) ≤ qf i) (hG : ∀ w, 0 ≤ G w)
    (j : ℕ) (u : ℕ → ℕ) : 0 ≤ nodeVal qf n ν γ G j u :=
  expect_nonneg (nu_mem_sufSet hν j) fun _ _ => hG _

theorem expVal_nonneg (hν : ∀ i < n, 0 ≤ ν (qf i) ∧ ν (qf i) ≤ qf i) (hG : ∀ w, 0 ≤ G w)
    {j : ℕ} (hj : j < n) (a : ℕ) (u : ℕ → ℕ) : 0 ≤ expVal qf n ν γ G j a u :=
  sum_nonneg fun _ _ => mul_nonneg (rho_nonneg (hν j hj).1 (hν j hj).2 _ _)
    (nodeVal_nonneg hν hG _ _)

/-- `τ_S(u + w[qf j ↦ x]) = τ_S(u)·(x+1)·τ_{sufSet (j+1)}(w)` for a prefix assignment `u`
(zero on `qf j, …`) and `w` supported on `sufSet (j+1)`. -/
theorem tauN_add_update (hinj : Set.InjOn qf (Set.Iio n)) {j : ℕ} (hj : j < n) {u w : ℕ → ℕ}
    (hu : ∀ i, j ≤ i → i < n → u (qf i) = 0) (hw : ∀ r, r ∉ sufSet qf n (j + 1) → w r = 0)
    (x : ℕ) :
    tauN (sufSet qf n 0) (u + Function.update w (qf j) x) =
      tauN (sufSet qf n 0) u * (x + 1) * tauN (sufSet qf n (j + 1)) w := by
  rw [tauN_sufSet hinj, tauN_sufSet hinj, tauN_sufSet hinj, ← range_eq_Ico,
    ← prod_range_mul_prod_Ico _ (Nat.le_of_lt hj), ← prod_range_mul_prod_Ico _ (Nat.le_of_lt hj),
    prod_eq_prod_Ico_succ_bot hj, prod_eq_prod_Ico_succ_bot hj]
  have hne : ∀ i < n, i ≠ j → qf i ≠ qf j := fun i hi hij h =>
    hij (hinj (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj) h)
  have h1 : ∏ i ∈ range j, ((u + Function.update w (qf j) x) (qf i) + 1) =
      ∏ i ∈ range j, (u (qf i) + 1) := by
    refine prod_congr rfl fun i hi => ?_
    have hij : i < j := mem_range.1 hi
    have hwi : w (qf i) = 0 := hw _ fun hmem => by
      obtain ⟨i', ⟨hi'1, hi'2⟩, hi'⟩ := mem_sufSet.1 hmem
      have := hinj (Set.mem_Iio.2 hi'2) (Set.mem_Iio.2 (by omega : i < n)) hi'
      omega
    simp [Function.update_of_ne (hne i (by omega) (by omega)), hwi]
  have h2 : ∏ i ∈ Ico (j + 1) n, ((u + Function.update w (qf j) x) (qf i) + 1) =
      ∏ i ∈ Ico (j + 1) n, (w (qf i) + 1) := by
    refine prod_congr rfl fun i hi => ?_
    have hi' := mem_Ico.1 hi
    simp [Function.update_of_ne (hne i hi'.2 (by omega)), hu i (by omega) hi'.2]
  have h3 : ∏ i ∈ Ico (j + 1) n, (u (qf i) + 1) = 1 := by
    refine prod_eq_one fun i hi => ?_
    have hi' := mem_Ico.1 hi
    simp [hu i (by omega) hi'.2]
  have h4 : (u + Function.update w (qf j) x) (qf j) = x := by
    simp [hu j le_rfl hj]
  rw [h1, h2, h3, h4, hu j le_rfl hj]
  ring

/-- **The pruning bound** (`dfsExp`'s `bnd`): if `0 ≤ G(w) ≤ C·τ_S(w)` for all `w`
(`S = sufSet qf n 0`), and the prefix assignment `u` vanishes on `qf j, …, qf (n−1)`, then
`expVal j a u ≤ τ_S(u)·h_γ(a)·(C·∏_{q ∈ sufSet (j+1)} (1 + ν_q/(q−1)))`. -/
theorem expVal_le (hinj : Set.InjOn qf (Set.Iio n)) (hq1 : ∀ i < n, 1 < qf i)
    (hν : ∀ i < n, 0 ≤ ν (qf i) ∧ ν (qf i) ≤ qf i) {C : ℝ} (hC : 0 ≤ C)
    (hG0 : ∀ w, 0 ≤ G w) (hG : ∀ w, G w ≤ C * (tauN (sufSet qf n 0) w : ℝ)) {j : ℕ} (hj : j < n)
    {u : ℕ → ℕ} (hu : ∀ i, j ≤ i → i < n → u (qf i) = 0) (a : ℕ) :
    expVal qf n ν γ G j a u ≤
      (tauN (sufSet qf n 0) u : ℝ) * hMass (qf j) (ν (qf j)) (γ (qf j)) a *
        (C * ∏ q ∈ sufSet qf n (j + 1), (1 + ν q / ((q : ℝ) - 1))) := by
  have hqj := qf_notMem_sufSet hinj hj
  have hνins : ∀ r ∈ insert (qf j) (sufSet qf n (j + 1)), 0 ≤ ν r ∧ ν r ≤ r := by
    rw [← sufSet_eq_insert hj]
    exact nu_mem_sufSet hν j
  have hνsuf := nu_mem_sufSet hν (qf := qf) (j + 1)
  have huj : u (qf j) = 0 := hu j le_rfl hj
  -- rewrite the node values as expectations of `f (update w (qf j) x)`, `f w = G (u + w)`
  have e : expVal qf n ν γ G j a u = ∑ x ∈ Ico a (γ (qf j) + 1),
      rho (qf j) (ν (qf j)) (γ (qf j)) x * expect (sufSet qf n (j + 1)) ν γ
        (fun w => G (u + Function.update w (qf j) x)) := by
    unfold expVal nodeVal
    refine sum_congr rfl fun x _ => ?_
    congr 1
    refine expect_congr_fun fun w hw => ?_
    have hwq : w (qf j) = 0 := (mem_box.1 hw).2 _ hqj
    rw [add_update_comm huj hwq]
  rw [e]
  have hK : (0 : ℝ) ≤ C * (tauN (sufSet qf n 0) u : ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
  have hmain := sum_tail_expect_le hνins γ (f := fun w => G (u + w))
    (K := C * (tauN (sufSet qf n 0) u : ℝ))
    (g := fun w => (tauN (sufSet qf n (j + 1)) w : ℝ)) (fun w hw x _ => by
      refine ⟨hG0 _, (hG _).trans (le_of_eq ?_)⟩
      have hw' : ∀ r, r ∉ sufSet qf n (j + 1) → w r = 0 := (mem_box.1 hw).2
      rw [tauN_add_update hinj hj hu hw' x]
      push_cast
      ring) a
  refine hmain.trans ?_
  have hE := expect_tauN_le (Ps := sufSet qf n (j + 1)) (ν := ν)
    (fun q hq => by obtain ⟨i, ⟨-, hi⟩, rfl⟩ := mem_sufSet.1 hq; exact hq1 i hi)
    (fun q hq => (hνsuf q hq).1) γ
  have hh := hMass_nonneg (hν j hj).1 (hν j hj).2 (γ (qf j)) a
  calc C * (tauN (sufSet qf n 0) u : ℝ) * hMass (qf j) (ν (qf j)) (γ (qf j)) a *
        expect (sufSet qf n (j + 1)) ν γ (fun w => (tauN (sufSet qf n (j + 1)) w : ℝ))
      ≤ C * (tauN (sufSet qf n 0) u : ℝ) * hMass (qf j) (ν (qf j)) (γ (qf j)) a *
        ∏ q ∈ sufSet qf n (j + 1), (1 + ν q / ((q : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg hK hh)
    _ = (tauN (sufSet qf n 0) u : ℝ) * hMass (qf j) (ν (qf j)) (γ (qf j)) a *
        (C * ∏ q ∈ sufSet qf n (j + 1), (1 + ν q / ((q : ℝ) - 1))) := by ring

end DFS

/-! ## `hingeLoss` in leaf form -/

/-- The profile of `n = s_S` on `B`: `a_q(n) = acount p m q n` for `q ∈ B`, `0` elsewhere. -/
def sbhProfile (p m : ℕ) (B : Finset ℕ) (n q : ℕ) : ℕ := if q ∈ B then acount p m q n else 0

/-- `c(d) = 1 − p^{1 − j0(d)} ≥ 0`. -/
theorem cc_nonneg {p : ℕ} (hp : 1 ≤ p) (m d : ℕ) : 0 ≤ cc p m d := by
  unfold cc
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have : ((p : ℝ)⁻¹) ^ (j0 p m d - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
  linarith

/-- `F(n) ≥ 0`. -/
theorem Fsum_nonneg {p : ℕ} (hp : 1 ≤ p) (m n : ℕ) : 0 ≤ Fsum p m n := by
  unfold Fsum
  exact sum_nonneg fun d _ => cc_nonneg hp m d

/-- `b` of the S/B/H identity as `bstat`. -/
theorem bstat_sbhProfile (p m : ℕ) {B : Finset ℕ} (H : Finset ℕ) (n : ℕ) (w : ℕ → ℕ) :
    (bstat (B ∪ H) (sbhProfile p m B n) w : ℝ) =
      ∑ q ∈ B with 1 ≤ w q, (acount p m q n : ℝ) := by
  unfold bstat
  rw [Nat.cast_sum, sum_filter]
  have e : ∀ q ∈ B ∪ H, (((if 1 ≤ w q then sbhProfile p m B n q else 0 : ℕ)) : ℝ) =
      if q ∈ B then (if 1 ≤ w q then (acount p m q n : ℝ) else 0) else 0 := by
    intro q _
    unfold sbhProfile
    by_cases h1 : 1 ≤ w q <;> by_cases h2 : q ∈ B <;> simp [h1, h2]
  rw [sum_congr rfl e, sum_ite_mem, union_inter_cancel_left]

/-- **`hingeLoss` in leaf form**: Fubini over `S` and `R = B ∪ H` after `hingeLoss_eq_sbh`:
`hingeLoss = E_S[u ↦ E_R[(τ_S(u)·T − (F(s_S(u)) + δ_p(p−1)) − (1 − 1/p)·b)⁺]] / ((p−1)(1−δ_p))`
with `b = bstat R (sbhProfile p m B (s_S(u)))`. -/
theorem hingeLoss_eq_sbhLeaf {m p y : ℕ} {δ : ℕ → ℝ} (hp : p.Prime) {S B H : Finset ℕ}
    (hpart : Nat.primesBelow p = S ∪ (B ∪ H)) (hSBH : Disjoint S (B ∪ H))
    (hB : ∀ q ∈ B, y ≤ q ∧ q * p < m) (hH : ∀ q ∈ H, m ≤ q * p) (hy2 : m ≤ y * y * p)
    (hy1 : m ≤ y * p ^ 2) (γ : ℕ → ℕ) :
    Main.hingeLoss m δ p γ =
      expect S (Main.tilt δ) γ (fun u => sbhLeaf (B ∪ H) (Main.tilt δ) γ
        (sbhProfile p m B (smooth S u)) (tauN S u)
        (Fsum p m (smooth S u) + δ p * ((p : ℝ) - 1)) (1 - 1 / (p : ℝ))) /
        (((p : ℝ) - 1) * (1 - δ p)) := by
  have hS : ∀ q ∈ S, q.Prime := fun q hq =>
    Nat.prime_of_mem_primesBelow (hpart ▸ mem_union_left _ hq)
  rw [hingeLoss_eq_sbh hp hpart hSBH hB hH hy2 hy1 γ]
  congr 1
  rw [hpart, expect_union hSBH]
  refine expect_congr_fun fun u hu => ?_
  unfold sbhLeaf
  refine expect_congr_fun fun w hw => ?_
  have huR : ∀ q ∈ B ∪ H, u q = 0 := fun q hq =>
    (mem_box.1 hu).2 q (fun hqS => disjoint_left.1 hSBH hqS hq)
  have hwS : ∀ q ∈ S, w q = 0 := fun q hq =>
    (mem_box.1 hw).2 q (fun hqR => disjoint_left.1 hSBH hq hqR)
  have hsm : smooth S (u + w) = smooth S u := by
    unfold smooth
    refine prod_congr rfl fun q hq => ?_
    simp [hwS q hq]
  have hT : ∏ q ∈ B ∪ H, (((u + w) q : ℕ) + (1 : ℝ)) = (tauN (B ∪ H) w : ℝ) := by
    rw [tauN_cast]
    refine prod_congr rfl fun q hq => ?_
    simp [huR q hq]
  have hb : ∑ q ∈ B with 1 ≤ (u + w) q, (acount p m q (smooth S u) : ℝ) =
      (bstat (B ∪ H) (sbhProfile p m B (smooth S u)) w : ℝ) := by
    rw [bstat_sbhProfile]
    refine sum_congr ?_ fun _ _ => rfl
    refine filter_congr fun q hq => ?_
    simp [huR q (mem_union_left _ hq)]
  rw [hsm, hT, hb, card_divisors_smooth_eq_tauN hS]
  congr 1
  ring

end MinModulus.Checker2Math.A
