import MinModulus.Checker2Sound.StatesH
import MinModulus.Checker2Math.SBHLaw

/-!
# `Checker2Sound.Tables` (agent L2-C): the lower-tail tables of the S/B/H bound (`buildTab_sound`)

STATUS: complete, no `sorry`. The DP step of the joint law `P(T = k ∧ b = j)` is L2-A's
`Checker2Math.A.lawJoint_insert_le` (module `Checker2Math/SBHLaw.lean`, STABLE); `buildTab_sound'` is
proved from its statement `JointStepSpec`, which `jointStepSpec_holds` discharges.

* `profileFn_get`, `profileFn_of_notMem`: the profile as a function on the primes;
* `lawJoint_zero_left'`, `lawJoint_eq_lawTau'` (the `H` part: zero profile);
* `RowsInv`: the rows `b ≤ bm` of the table hold upper bounds of `P(T = ·, b)` on `[0, K]`;
  `RowsInv_init` (rows from the `T_H` law), `RowsInv_step` (`rowsStep`), `RowsInv_rowsAll`;
* the prefix tables: `tab_row_bound` (`Σ_{j ≤ ⌊c⌋} (c − j) P(T = j, b) ≤ c·pv S0 − wv S1W`);
* `ebLoW_le` (`wv EbW ≤ Σ_B a_q ν_q/q`);
* **`buildTab_sound'`** (from `JointStepSpec`) and **`buildTab_sound`**.
-/

namespace MinModulus.Checker2Sound.C

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Main MinModulus.Smooth MinModulus.Checker2Sound

/-! ### The DP step of the joint law (L2-A) -/

/-- L2-A's `Checker2Math.A.lawJoint_insert_le`, verbatim (the DP step of `P(T = ·, b = ·)` with upper
bounds, push form on `[0, K]`). -/
def JointStepSpec : Prop :=
  ∀ {q : ℕ} {R : Finset ℕ} (_ : q ∉ R) {ν : ℕ → ℝ}
    (_ : ∀ r ∈ insert q R, 0 ≤ ν r ∧ ν r ≤ r) (a : ℕ → ℕ) (γ : ℕ → ℕ) {K : ℕ} (_ : 0 < K)
    (D : ℕ → ℕ → ℝ) (ℓ : ℕ → ℝ) {j : ℕ}
    (_ : ∀ t ≤ K, ∀ i ≤ j, lawJoint R a ν γ t i ≤ D t i)
    (_ : ∀ x < K, rho q (ν q) (γ q) x ≤ ℓ x) {T : ℕ} (_ : T ≤ K),
    lawJoint (insert q R) a ν γ T j ≤
      ℓ 0 * D T j +
      (if a q ≤ j then ∑ t ∈ range (K + 1), ∑ x ∈ Ico 1 K, if t * (x + 1) = T then
          ℓ x * D t (j - a q) else 0
        else 0)

/-- `T ≥ 1`: no mass at `T = 0`. -/
theorem lawJoint_zero_left' (R : Finset ℕ) (a : ℕ → ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) (j : ℕ) :
    lawJoint R a ν γ 0 j = 0 := by
  unfold lawJoint
  refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const R ν γ 0)
  have : ¬ (tauN R v = 0 ∧ bstat R a v = j) := fun h => (tauN_pos R v).ne' h.1
  simp [this]

/-- A zero profile on `R`: `P(T = k ∧ b = j) = [j = 0]·P(T = k)`. -/
theorem lawJoint_eq_lawTau' {R : Finset ℕ} {a : ℕ → ℕ} (h : ∀ q ∈ R, a q = 0) (ν : ℕ → ℝ)
    (γ : ℕ → ℕ) (k j : ℕ) : lawJoint R a ν γ k j = if j = 0 then lawTau R ν γ k else 0 := by
  have hb : ∀ w, bstat R a w = 0 := fun w => by
    unfold bstat
    exact sum_eq_zero fun q hq => by simp [h q hq]
  unfold lawJoint lawTau
  split_ifs with hj
  · subst hj
    exact expect_congr_fun fun v _ => by simp [hb v]
  · refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const R ν γ 0)
    have : ¬ (tauN R v = k ∧ bstat R a v = j) := fun h' => hj (by rw [← h'.2, hb v])
    simp [this]

/-! ### The profile as a function -/

theorem profileFn_get {Bq a : Array ℕ} (hnd : Bq.toList.Nodup) {i : ℕ} (hi : i < Bq.size) :
    profileFn Bq a Bq[i]! = a[i]! := by
  unfold profileFn
  have hi' : i < Bq.toList.length := by simpa using hi
  rw [aget_eq_list hi', hnd.idxOf_getElem i hi']

theorem profileFn_of_notMem {Bq a : Array ℕ} (ha : a.size = Bq.size) {q : ℕ}
    (hq : q ∉ Bq.toList) : profileFn Bq a q = 0 := by
  unfold profileFn
  rw [List.idxOf_eq_length hq, Array.length_toList, ← ha, aget_of_size_le a le_rfl]
  rfl

/-! ### The rows invariant -/

/-- The rows `b ≤ bm` of a lower-tail table, columns `[0, K]`, hold upper bounds of the joint law
`P_R(T = ·, b)` (profile `af`), for every cap `N ≥ KH`. -/
structure RowsInv (P : Params2) (R : Finset ℕ) (af : ℕ → ℕ) (bm K : ℕ)
    (rows : Array (Array ℕ)) : Prop where
  size : rows.size = bm + 1
  rsize : ∀ b ≤ bm, (rows[b]!).size = K + 1
  law : ∀ N, P.KH ≤ N → ∀ b ≤ bm, ∀ T ≤ K,
    lawJoint R af (nu2 P) (fun _ => N) T b ≤ pv ((rows[b]!)[T]!)

/-- **One `rowsStep`** (a `B` prime `q`, increment `af q`, point masses `pmArr q dn (KH − 1)`). -/
theorem RowsInv_step (hspec : JointStepSpec) {P : Params2} {R : Finset ℕ} {af : ℕ → ℕ}
    {bm K : ℕ} {rows : Array (Array ℕ)} (h : RowsInv P R af bm K rows)
    (hR : ∀ q ∈ R, q.Prime ∧ q ≤ P.X) (hK : K ≤ P.KH) {q : ℕ} (hq : q.Prime) (hqX : q ≤ P.X)
    (hqR : q ∉ R) :
    RowsInv P (insert q R) af bm K (rowsStep rows K (af q) (pmArr q (deltaN2 P q) (P.KH - 1))) := by
  have hq2 := hq.two_le
  have hνi : ∀ r ∈ insert q R, 0 ≤ nu2 P r ∧ nu2 P r ≤ r := fun r hr => by
    rcases mem_insert.1 hr with rfl | hr
    · exact nu2_mem hq2 hqX
    · exact nu2_mem (hR r hr).1.two_le (hR r hr).2
  set pm := pmArr q (deltaN2 P q) (P.KH - 1) with hpm
  refine ⟨by rw [rowsStep_size, h.size], fun b hb => ?_, fun N hN b hb T hT => ?_⟩
  · rw [rowsStep_get _ _ _ _ (by rw [h.size]; omega), rowNew_size]
  rw [rowsStep_get _ _ _ _ (by rw [h.size]; omega)]
  rcases Nat.eq_zero_or_pos T with rfl | hT1
  · rw [lawJoint_zero_left']
    exact pv_nonneg _
  have hK0 : 0 < K := by omega
  refine (hspec hqR hνi af (fun _ => N) hK0 (fun t i => pv ((rows[i]!)[t]!)) (fun x => pv pm[x]!)
    (fun t ht i hi => h.law N hN i (by omega) t ht)
    (fun x hx => rho_nu2_le_pmArr hq2 hqX (by omega) (by omega)) hT).trans ?_
  rw [rowNew_get _ _ _ _ _ hT, pv_add]
  refine add_le_add ?_ ?_
  · rw [sum_ite_eq' (Ico 1 (K + 1)) T (fun t => mulUp (rows[b]!)[t]! pm[0]!),
      ite_eq_left (mem_Ico.2 ⟨hT1, by omega⟩), mul_comm]
    exact pv_mulUp _ _
  · split_ifs with hs
    · rw [pv_sum, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < K + 1)]
      rw [sum_eq_zero (s := Ico 1 K) fun x _ => ite_eq_right (by omega), zero_add]
      refine sum_le_sum fun t _ => ?_
      rw [pv_sum]
      refine sum_le_sum fun x _ => ?_
      rw [pv_ite]
      split_ifs
      · rw [mul_comm]
        exact pv_mulUp _ _
      · exact le_rfl
    · exact pv_nonneg _

theorem notMem_take_of_nodup {l : List ℕ} (hnd : l.Nodup) {i : ℕ} (hi : i < l.length) :
    l[i] ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.1 hm
  have := (hnd.getElem_inj_iff).1 he
  omega

theorem take_succ_toFinset {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    (l.take (i + 1)).toFinset = insert l[i] (l.take i).toFinset := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.toFinset_append,
    List.toFinset_cons, List.toFinset_nil, insert_empty, union_comm, ← insert_eq]

/-- **The loop `rowsAll`**: after the `B` primes of index `[i, a.size)`, the rows hold the joint law
over `B ∪ H` (`H` = `RH`). -/
theorem RowsInv_rowsAll (hspec : JointStepSpec) {P : Params2} {Bq Bdn a : Array ℕ}
    (hBq : ∀ q ∈ Bq.toList, q.Prime ∧ q ≤ P.X) (hBnd : Bq.toList.Nodup)
    (hBdn : Bdn = Bq.map (deltaN2 P)) (ha : a.size = Bq.size) {RH : Finset ℕ}
    (hRH : ∀ q ∈ RH, q.Prime ∧ q ≤ P.X) (hBH : Disjoint Bq.toList.toFinset RH) {bm K : ℕ}
    (hK : K ≤ P.KH) :
    ∀ (f i : ℕ) (rows : Array (Array ℕ)), i + f = a.size →
      RowsInv P ((Bq.toList.take i).toFinset ∪ RH) (profileFn Bq a) bm K rows →
      RowsInv P (Bq.toList.toFinset ∪ RH) (profileFn Bq a) bm K
        (rowsAll a ((Array.range Bq.size).map fun i => pmArr Bq[i]! Bdn[i]! (P.KH - 1)) K rows
          i f) := by
  intro f
  induction f with
  | zero =>
    intro i rows hi h
    rw [rowsAll.eq_1]
    rw [Nat.add_zero, ha] at hi
    subst hi
    rwa [← Array.length_toList, List.take_length] at h
  | succ f ih =>
    intro i rows hi h
    rw [rowsAll.eq_2]
    have hiB : i < Bq.size := by omega
    have hiL : i < Bq.toList.length := by simpa using hiB
    set q := Bq[i]! with hqdef
    have hqL : Bq.toList[i] = q := (aget_eq_list hiL).symm
    have hqmem : q ∈ Bq.toList := hqL ▸ List.getElem_mem hiL
    have hpmB : ((Array.range Bq.size).map fun i => pmArr Bq[i]! Bdn[i]! (P.KH - 1))[i]! =
        pmArr q (deltaN2 P q) (P.KH - 1) := by
      rw [aget_range_map _ _ hiB, hBdn, aget_map _ _ hiB]
    rw [hpmB, ← profileFn_get (a := a) hBnd hiB]
    refine ih (i + 1) _ (by omega) ?_
    have hqR : q ∉ (Bq.toList.take i).toFinset ∪ RH := by
      rw [mem_union, not_or, List.mem_toFinset]
      refine ⟨hqL ▸ notMem_take_of_nodup hBnd hiL, fun hm => ?_⟩
      exact disjoint_left.1 hBH (List.mem_toFinset.2 hqmem) hm
    have hR : ∀ r ∈ (Bq.toList.take i).toFinset ∪ RH, r.Prime ∧ r ≤ P.X := by
      intro r hr
      rcases mem_union.1 hr with hr | hr
      · exact hBq r (List.mem_of_mem_take (List.mem_toFinset.1 hr))
      · exact hRH r hr
    have h' := RowsInv_step hspec h hR hK (hBq q hqmem).1 (hBq q hqmem).2 hqR
    rwa [take_succ_toFinset hiL, hqL, insert_union]

/-- The initial rows: row `0` is the `T_H` law (`H.D` restricted to `[0, K]`), rows `1 … bm` are `0`. -/
theorem RowsInv_init {P : Params2} {H : HState} (hH : HValid P H)
    {Bq a : Array ℕ} (ha : a.size = Bq.size)
    (hBH : Disjoint Bq.toList.toFinset (idxSet P H.lo H.hi)) {bm K : ℕ} (hK : K ≤ P.KH) :
    RowsInv P (idxSet P H.lo H.hi) (profileFn Bq a) bm K
      ((Array.replicate (bm + 1) (zeros (K + 1))).set! 0 (H.D.extract 0 (K + 1))) := by
  have hz : ∀ q ∈ idxSet P H.lo H.hi, profileFn Bq a q = 0 := fun q hq =>
    profileFn_of_notMem ha fun hm => disjoint_left.1 hBH (List.mem_toFinset.2 hm) hq
  have hget : ∀ b ≤ bm, ((Array.replicate (bm + 1) (zeros (K + 1))).set! 0
      (H.D.extract 0 (K + 1)))[b]! = if b = 0 then H.D.extract 0 (K + 1) else zeros (K + 1) := by
    intro b hb
    rw [aget_set, Array.size_replicate, aget_replicate]
    by_cases hb0 : b = 0
    · rw [ite_eq_left ⟨hb0.symm, by omega⟩, ite_eq_left hb0]
    · rw [ite_eq_right (fun h => hb0 h.1.symm), ite_eq_right hb0, ite_eq_left (by omega)]
  refine ⟨by rw [size_set, Array.size_replicate], fun b hb => ?_, fun N hN b hb T hT => ?_⟩
  · rw [hget b hb]
    split_ifs
    · rw [Array.size_extract, hH.size]
      omega
    · exact size_zeros _
  · rw [lawJoint_eq_lawTau' hz, hget b hb]
    split_ifs with hb0
    · rw [aget_extract _ _ _ (by omega)]
      exact hH.law N hN T (by omega)
    · exact pv_nonneg _

/-! ### Prefix tables and `EbW` -/

/-- `wv (x >>> 14) ≤ pv x`. -/
theorem wv_shiftRight_le (x : ℕ) : wv (x >>> 14) ≤ pv x := by
  unfold wv pv
  rw [Nat.shiftRight_eq_div_pow]
  have h1 : ((x / 2 ^ 14 : ℕ) : ℝ) ≤ (x : ℝ) / 2 ^ 14 := by
    have := Nat.cast_div_le (α := ℝ) (m := x) (n := 2 ^ 14)
    rwa [Nat.cast_pow, Nat.cast_ofNat] at this
  have e : (x : ℝ) / 2 ^ 62 = ((x : ℝ) / 2 ^ 14) / 2 ^ 48 := by
    rw [div_div]
    norm_num
  rw [e]
  exact div_le_div_of_nonneg_right h1 (by positivity)

/-- **The row bound**: with `D` = one row (upper bounds `P(T = j, b) ≤ pv D[j]` for `j ≤ ⌊c⌋`),
`Σ_{j ≤ ⌊c⌋} (c − j)·P(T = j, b) ≤ c·pv S0[⌊c⌋] − wv (S1[⌊c⌋] >>> 14)`. -/
theorem tab_row_bound (D : Array ℕ) (L : ℕ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ j ≤ ⌊c⌋₊, L j ≤ pv D[j]!) :
    ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * L j ≤
      c * pv (pS0 D ⌊c⌋₊) - wv (pS1 D ⌊c⌋₊ >>> 14) := by
  have h1 : ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * L j ≤
      ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * pv D[j]! := by
    refine sum_le_sum fun j hj => ?_
    have hj' : j ≤ ⌊c⌋₊ := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hcj : (j : ℝ) ≤ c := (Nat.cast_le.2 hj').trans (Nat.floor_le hc)
    exact mul_le_mul_of_nonneg_left (hL j hj') (by linarith)
  have h2 : ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * pv D[j]! = c * pv (pS0 D ⌊c⌋₊) - pv (pS1 D ⌊c⌋₊) := by
    unfold pS0 pS1
    rw [pv_sum, pv_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [pv_natMul]
    ring
  rw [h2] at h1
  linarith [wv_shiftRight_le (pS1 D ⌊c⌋₊)]

/-- `Σ_{q ∈ l.toFinset} f q = Σ_{i < |l|} f l[i]` for a duplicate-free list. -/
theorem sum_toFinset_eq_sum_range {l : List ℕ} (hnd : l.Nodup) (f : ℕ → ℝ) :
    ∑ q ∈ l.toFinset, f q = ∑ i ∈ range l.length, f l[i]! := by
  rw [List.sum_toFinset f hnd]
  clear hnd
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ', List.getElem!_cons_zero,
      add_comm]
    simp only [List.getElem!_cons_succ]

/-- **`EbW`**: `wv (ebLoW a Bq Bdn) ≤ Σ_{q ∈ B} a_q ν_q/q`. -/
theorem ebLoW_le {P : Params2} {Bq Bdn a : Array ℕ} (hBq : ∀ q ∈ Bq.toList, q.Prime ∧ q ≤ P.X)
    (hBnd : Bq.toList.Nodup) (hBdn : Bdn = Bq.map (deltaN2 P)) (ha : a.size = Bq.size) :
    wv (ebLoW a Bq Bdn) ≤ ∑ q ∈ Bq.toList.toFinset, (profileFn Bq a q : ℝ) * (nu2 P q / q) := by
  rw [sum_toFinset_eq_sum_range hBnd, Array.length_toList, ebLoW_eq, ha]
  unfold wv
  rw [Nat.cast_sum, sum_div]
  refine sum_le_sum fun i hi => ?_
  have hiB : i < Bq.size := mem_range.1 hi
  have hiL : i < Bq.toList.length := by simpa using hiB
  rw [Array.getElem!_toList, profileFn_get hBnd hiB]
  have hq := hBq _ (List.getElem_mem hiL)
  rw [← aget_eq_list hiL] at hq
  set q := Bq[i]!
  have hdn : Bdn[i]! = deltaN2 P q := by rw [hBdn, aget_map _ _ hiB]
  rw [hdn]
  have hnd := MinModulus.CheckerSound.B.nuDen_pos (deltaN2_lt P q)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1.pos
  have hnd0 : (0 : ℝ) < ((nuDen (deltaN2 P q) : ℕ) : ℝ) := by exact_mod_cast hnd
  push_cast
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h1 : ((DDEN * W48 / (nuDen (deltaN2 P q) * q) : ℕ) : ℝ) ≤
      ((DDEN * W48 : ℕ) : ℝ) / ((nuDen (deltaN2 P q) * q : ℕ) : ℝ) := Nat.cast_div_le
  have e : ((DDEN * W48 : ℕ) : ℝ) / ((nuDen (deltaN2 P q) * q : ℕ) : ℝ) / 2 ^ 48 =
      nu2 P q / q := by
    rw [nu2_eq_tiltN hq.2, MinModulus.CheckerSound.B.tiltN_eq_div_nuDen (deltaN2_lt P q), W48_eq]
    push_cast
    rw [MinModulus.CheckerSound.B.cast_DDEN]
    field_simp
    norm_num
  calc ((DDEN * W48 / (nuDen (deltaN2 P q) * q) : ℕ) : ℝ) / 2 ^ 48
      ≤ ((DDEN * W48 : ℕ) : ℝ) / ((nuDen (deltaN2 P q) * q : ℕ) : ℝ) / 2 ^ 48 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = nu2 P q / q := e

/-! ### `buildTab` -/

/-- **`buildTab_sound` from the DP step of the joint law** (`JointStepSpec`, L2-A). -/
theorem buildTab_sound' (hspec : JointStepSpec) (P : Params2) (hPX : P.PX ≤ P.X) {H : HState}
    (hH : HValid P H) {Bq Bdn a : Array ℕ}
    (hBq : ∀ q ∈ Bq.toList, q.Prime ∧ q ≤ P.X) (hBnd : Bq.toList.Nodup)
    (hBH : Disjoint Bq.toList.toFinset (idxSet P H.lo H.hi))
    (hBdn : Bdn = Bq.map (deltaN2 P)) (ha : a.size = Bq.size) (tp1int : ℕ) (N : ℕ)
    (hN : P.KH ≤ N) :
    let tab := buildTab a Bq Bdn ((Array.range Bq.size).map fun i =>
      pmArr Bq[i]! Bdn[i]! (P.KH - 1)) H.D P.KH tp1int
    let R := Bq.toList.toFinset ∪ idxSet P H.lo H.hi
    tab.bm = a.foldl (· + ·) 0 ∧
      wv tab.EbW ≤ ∑ q ∈ Bq.toList.toFinset, (profileFn Bq a q : ℝ) * (nu2 P q / q) ∧
      ∀ b, b ≤ tab.bm → ∀ c : ℝ, 0 ≤ c → ⌊c⌋₊ ≤ tab.K →
        ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * lawJoint R (profileFn Bq a) (nu2 P) (fun _ => N) j b ≤
          c * pv (tabS0 tab b ⌊c⌋₊) - wv (tabS1W tab b ⌊c⌋₊) := by
  intro tab R
  refine ⟨rfl, ebLoW_le hBq hBnd hBdn ha, fun b hb c hc hcK => ?_⟩
  -- unfold the table
  set bm := a.foldl (· + ·) 0 with hbm
  set K := min P.KH (tp1int + 2 + bm) with hKdef
  set pmB := (Array.range Bq.size).map fun i => pmArr Bq[i]! Bdn[i]! (P.KH - 1) with hpmB
  set rows0 := (Array.replicate (bm + 1) (zeros (K + 1))).set! 0 (H.D.extract 0 (K + 1))
    with hrows0
  set rows := rowsAll a pmB K rows0 0 a.size with hrows
  have hK : K ≤ P.KH := min_le_left _ _
  have hRH : ∀ q ∈ idxSet P H.lo H.hi, q.Prime ∧ q ≤ P.X := fun q hq =>
    ⟨(idxSet_mem hq).1, (idxSet_mem hq).2.trans hPX⟩
  have h0 : RowsInv P ((Bq.toList.take 0).toFinset ∪ idxSet P H.lo H.hi) (profileFn Bq a) bm K
      rows0 := by
    rw [List.take_zero, List.toFinset_nil, empty_union]
    exact RowsInv_init hH ha hBH hK
  have hI := RowsInv_rowsAll hspec hBq hBnd hBdn ha hRH hBH hK a.size 0 rows0 (by omega) h0
  have hbt : tab.bm = bm := rfl
  have hKt : tab.K = K := rfl
  rw [hbt] at hb
  rw [hKt] at hcK
  have hbr : b < rows.size := by rw [hI.size]; omega
  have hrs : (rows[b]!).size = K + 1 := hI.rsize b hb
  have hS0 : tabS0 tab b ⌊c⌋₊ = pS0 rows[b]! ⌊c⌋₊ := by
    show (((rows.map prefixTables).map (·.1))[b]!)[⌊c⌋₊]! = _
    rw [aget_map _ _ (by rw [Array.size_map]; exact hbr), aget_map _ _ hbr]
    exact ((prefixTables_spec rows[b]!).2.2 ⌊c⌋₊ (by omega)).1
  have hS1 : tabS1W tab b ⌊c⌋₊ = pS1 rows[b]! ⌊c⌋₊ >>> 14 := by
    show (((rows.map prefixTables).map (·.2.map (· >>> 14)))[b]!)[⌊c⌋₊]! = _
    rw [aget_map _ _ (by rw [Array.size_map]; exact hbr), aget_map _ _ hbr,
      aget_map _ _ (by rw [(prefixTables_spec rows[b]!).2.1]; omega)]
    rw [((prefixTables_spec rows[b]!).2.2 ⌊c⌋₊ (by omega)).2]
  rw [hS0, hS1]
  exact tab_row_bound rows[b]! _ hc fun j hj => hI.law N hN b hb j (by omega)

/-- L2-A's DP step discharges `JointStepSpec`. -/
theorem jointStepSpec_holds : JointStepSpec := by
  intro q R hq ν hν a γ K hK D ℓ j hD hℓ T hT
  exact A.lawJoint_insert_le hq hν a γ hK D ℓ hD hℓ hT

/-- **(L2-C → L2-D)** The lower-tail table of one profile. With `R = B ∪ H` (`B` = the primes of
`Bq`, `H = idxSet P H.lo H.hi`, disjoint) and the profile `a` (`profileFn Bq a`, zero off `B`),
for every cap `N ≥ KH`:
* `bm = Σ a` and `E[b] ≥ wv EbW`;
* for every row `b ≤ bm` and every real `c ≥ 0` with `⌊c⌋ ≤ K`:
  `Σ_{j ≤ ⌊c⌋} (c − j)·P(T = j ∧ b) ≤ c·pv S0[b][⌊c⌋] − wv S1W[b][⌊c⌋]`
(code: `buildTab`, `rowsAll`, `rowsStep`, `dpRange`, `prefixTables`, `ebLoW`; math: the
`lawJoint` recursion of L2-A). -/
theorem buildTab_sound (P : Params2) (hPX : P.PX ≤ P.X) {H : HState} (hH : HValid P H)
    {Bq Bdn a : Array ℕ}
    (hBq : ∀ q ∈ Bq.toList, q.Prime ∧ q ≤ P.X) (hBnd : Bq.toList.Nodup)
    (hBH : Disjoint Bq.toList.toFinset (idxSet P H.lo H.hi))
    (hBdn : Bdn = Bq.map (deltaN2 P)) (ha : a.size = Bq.size) (tp1int : ℕ) (N : ℕ)
    (hN : P.KH ≤ N) :
    let tab := buildTab a Bq Bdn ((Array.range Bq.size).map fun i =>
      pmArr Bq[i]! Bdn[i]! (P.KH - 1)) H.D P.KH tp1int
    let R := Bq.toList.toFinset ∪ idxSet P H.lo H.hi
    tab.bm = a.foldl (· + ·) 0 ∧
      wv tab.EbW ≤ ∑ q ∈ Bq.toList.toFinset, (profileFn Bq a q : ℝ) * (nu2 P q / q) ∧
      ∀ b, b ≤ tab.bm → ∀ c : ℝ, 0 ≤ c → ⌊c⌋₊ ≤ tab.K →
        ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * lawJoint R (profileFn Bq a) (nu2 P) (fun _ => N) j b ≤
          c * pv (tabS0 tab b ⌊c⌋₊) - wv (tabS1W tab b ⌊c⌋₊) :=
  buildTab_sound' jointStepSpec_holds P hPX hH hBq hBnd hBH hBdn ha tp1int N hN

end MinModulus.Checker2Sound.C
