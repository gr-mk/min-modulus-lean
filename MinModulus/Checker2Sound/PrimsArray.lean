import MinModulus.Checker2Impl.Checker
import MinModulus.CheckerSound.TauDPArray

/-!
# `Checker2Sound.PrimsArray` (agent L2-C): ℕ-level semantics of the loops of `Checker2Impl`

STATUS: complete, no `sorry` (agent L2-C, lean2 stage 2). Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

Pure `ℕ`-level statements about the loops of `Checker2Impl/Laws.lean`, `SBH.lean`, `TauSplit.lean`
(no rounding analysis, no probability): what each array entry *is*, as a finite sum. The real-number
statements (`PrimsReal.lean`) and the DP-state invariants (`States*.lean`, `Tables.lean`) are derived
from these. Namespace `MinModulus.Checker2Sound.C`.

* array access for any inhabited element type: `aget_def`, `aget_push`, `aget_set`, `size_set`,
  `aget_replicate`, `aget_of_size_le`, `aget_map`, `aget_extract`, `aget_zeros`;
* **`dpRange`** (the DP primitive): `dpRange_size`, `dpRange_get` (push form
  `Dn'[T] = Dn[T] + Σ_{1 ≤ t ≤ K} Σ_{alo ≤ a < ahi} [t(a+1) = T] mulUp D[t] pm[a]`, `T ≤ K < Dn.size`);
* `pmArr` (`pmArr_size`, `pmArr_get`: entries `pmE q dn a`), `hArr` (`hArr_size`, `hArr_get`),
  `weightByTau`, `weightByPow2`, `acut60_le` (`acut60 q ≤ 60` for `q ≥ 2`);
* `lostSumW_eq` (a finite sum), `prefixTables_spec`, `suffixTablesW_spec`;
* the e-law loops `eInner_spec`, `eOuter_spec`, `ELaw.add` (`eLawAdd_W`, `eLawAdd_lost`);
* the S/B/H tables: `ebLoW_eq`, `rowsStep_size`, `rowsStep_get` (`rowNew`), `rowNew_size`,
  `rowNew_get`.
-/

namespace MinModulus.Checker2Sound.C

open MinModulus.CheckerImpl MinModulus.Checker2Impl Finset

/-! ### Array access (any inhabited element type) -/

theorem aget_def {α : Type} [Inhabited α] (xs : Array α) (i : ℕ) :
    xs[i]! = xs[i]?.getD default := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem aget_push {α : Type} [Inhabited α] (xs : Array α) (x : α) (j : ℕ) :
    (xs.push x)[j]! = if j = xs.size then x else xs[j]! := by
  rw [aget_def, aget_def, Array.getElem?_push]
  split_ifs <;> simp

theorem size_set {α : Type} (xs : Array α) (i : ℕ) (v : α) : (xs.set! i v).size = xs.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem aget_set {α : Type} [Inhabited α] (xs : Array α) (i : ℕ) (v : α) (j : ℕ) :
    (xs.set! i v)[j]! = if i = j ∧ i < xs.size then v else xs[j]! := by
  rw [aget_def, aget_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < xs.size <;> simp [h2]
  · simp [h1]

theorem aget_replicate {α : Type} [Inhabited α] (n : ℕ) (v : α) (j : ℕ) :
    (Array.replicate n v)[j]! = if j < n then v else default := by
  rw [aget_def, Array.getElem?_replicate]
  split_ifs <;> simp

theorem aget_zeros (n j : ℕ) : (zeros n)[j]! = 0 := by
  unfold zeros
  rw [aget_replicate]
  split_ifs <;> rfl

theorem size_zeros (n : ℕ) : (zeros n).size = n := by
  unfold zeros
  exact Array.size_replicate

theorem aget_of_size_le {α : Type} [Inhabited α] (xs : Array α) {i : ℕ} (h : xs.size ≤ i) :
    xs[i]! = default := by
  rw [aget_def, Array.getElem?_eq_none h]
  rfl

theorem aget_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (xs : Array α) {i : ℕ}
    (h : i < xs.size) : (xs.map f)[i]! = f xs[i]! := by
  rw [aget_def, aget_def, Array.getElem?_map, Array.getElem?_eq_getElem h]
  simp

theorem aget_extract {α : Type} [Inhabited α] (xs : Array α) (stop i : ℕ) (h : i < stop) :
    (xs.extract 0 stop)[i]! = xs[i]! := by
  rw [aget_def, aget_def, Array.getElem?_extract]
  by_cases hi : i < xs.size
  · rw [ite_eq_left (by omega), Nat.zero_add]
  · rw [ite_eq_right (by omega), Array.getElem?_eq_none (by omega)]

theorem aget_range_map {α : Type} [Inhabited α] (n : ℕ) (f : ℕ → α) {i : ℕ} (h : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [aget_def, Array.getElem?_map, Array.getElem?_range, ite_eq_left h]
  rfl

theorem mulUp_zero_left' (y : ℕ) : mulUp 0 y = 0 := MinModulus.CheckerSound.B.mulUp_zero_left y

/-! ### `dpRange`, the DP primitive -/

theorem dpRange_inner_size (K : ℕ) (pm : Array ℕ) (d t : ℕ) :
    ∀ (a f : ℕ) (Dn : Array ℕ), (dpRange.inner K pm d t a f Dn).size = Dn.size := by
  intro a f
  induction f generalizing a with
  | zero => intro Dn; rfl
  | succ f ih =>
    intro Dn
    rw [dpRange.inner.eq_2]
    split_ifs
    · rw [ih, size_set]
    · rfl

/-- The inner loop adds `mulUp d pm[a']` at `t(a'+1)` for `a' ∈ [a, a + f)` (the early exit
drops only indices `> K`). -/
theorem dpRange_inner_get (K : ℕ) (pm : Array ℕ) (d t : ℕ) :
    ∀ (a f : ℕ) (Dn : Array ℕ), K < Dn.size → ∀ {T : ℕ}, T ≤ K →
      (dpRange.inner K pm d t a f Dn)[T]! =
        Dn[T]! + ∑ a' ∈ Ico a (a + f), if t * (a' + 1) = T then mulUp d pm[a']! else 0 := by
  intro a f
  induction f generalizing a with
  | zero => intro Dn _ T _; simp [dpRange.inner.eq_1]
  | succ f ih =>
    intro Dn hK T hT
    rw [dpRange.inner.eq_2]
    split_ifs with h
    · rw [ih (a + 1) _ (by rw [size_set]; exact hK) hT, aget_set,
        sum_eq_sum_Ico_succ_bot (by omega : a < a + (f + 1)),
        show a + 1 + f = a + (f + 1) by omega]
      by_cases hTa : t * (a + 1) = T
      · rw [ite_eq_left ⟨hTa, by omega⟩, ite_eq_left hTa, hTa]
        omega
      · rw [ite_eq_right (fun h' => hTa h'.1), ite_eq_right hTa]
        omega
    · have hz : ∀ a' ∈ Ico a (a + (f + 1)),
          (if t * (a' + 1) = T then mulUp d pm[a']! else 0) = 0 := by
        intro a' ha'
        have h1 : t * (a + 1) ≤ t * (a' + 1) :=
          Nat.mul_le_mul_left _ (by simp only [mem_Ico] at ha'; omega)
        rw [ite_eq_right (by omega)]
      rw [sum_congr rfl hz, sum_const_zero, Nat.add_zero]

theorem dpRange_outer_size (D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) :
    ∀ (t f : ℕ) (Dn : Array ℕ), (dpRange.outer D K pm alo ahi t f Dn).size = Dn.size := by
  intro t f
  induction f generalizing t with
  | zero => intro Dn; rfl
  | succ f ih =>
    intro Dn
    rw [dpRange.outer.eq_2, ih]
    split_ifs
    · rfl
    · rw [dpRange_inner_size]

theorem Ico_add_sub_eq (alo ahi : ℕ) : Ico alo (alo + (ahi - alo)) = Ico alo ahi := by
  rcases le_total alo ahi with h | h
  · rw [Nat.add_sub_cancel' h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, Ico_self, Ico_eq_empty_of_le h]

theorem dpRange_outer_get (D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) :
    ∀ (t f : ℕ) (Dn : Array ℕ), K < Dn.size → ∀ {T : ℕ}, T ≤ K →
      (dpRange.outer D K pm alo ahi t f Dn)[T]! =
        Dn[T]! + ∑ t' ∈ Ico t (t + f), ∑ a ∈ Ico alo ahi,
          if t' * (a + 1) = T then mulUp D[t']! pm[a]! else 0 := by
  intro t f
  induction f generalizing t with
  | zero => intro Dn _ T _; simp [dpRange.outer.eq_1]
  | succ f ih =>
    intro Dn hK T hT
    have hsz : K < (if (D[t]! == 0) = true then Dn else
        dpRange.inner K pm D[t]! t alo (ahi - alo) Dn).size := by
      split_ifs
      · exact hK
      · rw [dpRange_inner_size]; exact hK
    rw [dpRange.outer.eq_2, ih (t + 1) _ hsz hT,
      sum_eq_sum_Ico_succ_bot (by omega : t < t + (f + 1)),
      show t + 1 + f = t + (f + 1) by omega]
    by_cases hd : D[t]! = 0
    · have hz : ∑ a ∈ Ico alo ahi,
          (if t * (a + 1) = T then mulUp D[t]! pm[a]! else 0) = 0 := by
        refine sum_eq_zero fun a _ => ?_
        rw [hd, mulUp_zero_left']
        split_ifs <;> rfl
      rw [ite_eq_left (by simp [hd]), hz]
      omega
    · rw [ite_eq_right (by simp [hd]), dpRange_inner_get K pm _ t alo _ Dn hK hT, Ico_add_sub_eq]
      omega

theorem dpRange_size (Dn D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) :
    (dpRange Dn D K pm alo ahi).size = Dn.size :=
  dpRange_outer_size D K pm alo ahi 1 K Dn

/-- **`dpRange` semantics** (push form, exact): for `T ≤ K < Dn.size`,
`Dn'[T] = Dn[T] + Σ_{1 ≤ t ≤ K} Σ_{alo ≤ a < ahi} [t (a+1) = T] mulUp D[t] pm[a]`. -/
theorem dpRange_get (Dn D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) (hK : K < Dn.size)
    {T : ℕ} (hT : T ≤ K) :
    (dpRange Dn D K pm alo ahi)[T]! =
      Dn[T]! + ∑ t ∈ Ico 1 (K + 1), ∑ a ∈ Ico alo ahi,
        if t * (a + 1) = T then mulUp D[t]! pm[a]! else 0 := by
  unfold dpRange
  rw [dpRange_outer_get D K pm alo ahi 1 K Dn hK hT, Nat.add_comm 1 K]

/-- `dpRange` on a fresh zero array. -/
theorem dpRange_zeros_get (D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) {T : ℕ}
    (hT : T ≤ K) :
    (dpRange (zeros (K + 1)) D K pm alo ahi)[T]! =
      ∑ t ∈ Ico 1 (K + 1), ∑ a ∈ Ico alo ahi,
        if t * (a + 1) = T then mulUp D[t]! pm[a]! else 0 := by
  rw [dpRange_get _ D K pm alo ahi (by rw [size_zeros]; omega) hT, aget_zeros, Nat.zero_add]

theorem dpRange_zeros_size (D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) :
    (dpRange (zeros (K + 1)) D K pm alo ahi).size = K + 1 := by
  rw [dpRange_size, size_zeros]

/-! ### `pmArr`, `hArr`, `weightByTau`, `weightByPow2`, `acut60` -/

/-- The entries of `pmArr q dn A` (numerators over `2^62`): `pm[0] = ⌈2^62 (q nd − 10^9)/(q nd)⌉`,
`pm[1] = ⌈2^62·10^9 (q−1)/(nd q²)⌉`, `pm[a+2] = ⌈pm[a+1]/q⌉` (`nd = nuDen dn`). -/
def pmE (q dn : ℕ) : ℕ → ℕ
  | 0 => ratUp2 (q * nuDen dn - DDEN) (q * nuDen dn)
  | 1 => ratUp2 (DDEN * (q - 1)) (nuDen dn * q * q)
  | a + 2 => cdiv (pmE q dn (a + 1)) q

theorem pmE_succ_succ (q dn a : ℕ) : pmE q dn (a + 2) = cdiv (pmE q dn (a + 1)) q := rfl

theorem pmArr_go_spec (q dn : ℕ) :
    ∀ (f a : ℕ) (acc : Array ℕ), 1 ≤ a → acc.size = a + 1 → (∀ i ≤ a, acc[i]! = pmE q dn i) →
      (pmArr.go q f (pmE q dn a) acc).size = a + 1 + f ∧
        ∀ i ≤ a + f, (pmArr.go q f (pmE q dn a) acc)[i]! = pmE q dn i := by
  intro f
  induction f with
  | zero =>
    intro a acc _ hs he
    exact ⟨hs, fun i hi => he i (by omega)⟩
  | succ f ih =>
    intro a acc ha hs he
    rw [pmArr.go.eq_2]
    have e : cdiv (pmE q dn a) q = pmE q dn (a + 1) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rfl
    rw [e]
    have h := ih (a + 1) (acc.push (pmE q dn (a + 1))) (by omega)
      (by rw [Array.size_push, hs]) (fun i hi => by
        rw [aget_push, hs]
        by_cases hia : i = a + 1
        · rw [ite_eq_left hia, hia]
        · rw [ite_eq_right hia]
          exact he i (by omega))
    refine ⟨by rw [h.1]; omega, fun i hi => h.2 i (by omega)⟩

theorem pmArr_spec (q dn A : ℕ) :
    (pmArr q dn A).size = A + 1 ∧ ∀ i ≤ A, (pmArr q dn A)[i]! = pmE q dn i := by
  unfold pmArr
  dsimp only
  split_ifs with hA
  · subst hA
    refine ⟨rfl, fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this
    rfl
  · have h := pmArr_go_spec q dn (A - 1) 1
      #[ratUp2 (q * nuDen dn - DDEN) (q * nuDen dn), ratUp2 (DDEN * (q - 1)) (nuDen dn * q * q)]
      le_rfl rfl (fun i hi => by
        rcases Nat.lt_or_ge i 1 with h | h
        · have : i = 0 := by omega
          subst this; rfl
        · have : i = 1 := by omega
          subst this; rfl)
    have e : pmE q dn 1 = ratUp2 (DDEN * (q - 1)) (nuDen dn * q * q) := rfl
    rw [e] at h
    exact ⟨by rw [h.1]; omega, fun i hi => h.2 i (by omega)⟩

theorem pmArr_size (q dn A : ℕ) : (pmArr q dn A).size = A + 1 := (pmArr_spec q dn A).1

theorem pmArr_get (q dn A : ℕ) {i : ℕ} (hi : i ≤ A) : (pmArr q dn A)[i]! = pmE q dn i :=
  (pmArr_spec q dn A).2 i hi

theorem hArr_go_spec (q dn : ℕ) :
    ∀ (f a : ℕ) (acc : Array ℕ), acc.size = a → (∀ i < a, acc[i]! = hUp q dn i) →
      (hArr.go q dn a f acc).size = a + f ∧
        ∀ i < a + f, (hArr.go q dn a f acc)[i]! = hUp q dn i := by
  intro f
  induction f with
  | zero =>
    intro a acc hs he
    exact ⟨hs, fun i hi => he i (by omega)⟩
  | succ f ih =>
    intro a acc hs he
    rw [hArr.go.eq_2]
    have h := ih (a + 1) (acc.push (hUp q dn a)) (by rw [Array.size_push, hs]) (fun i hi => by
      rw [aget_push, hs]
      by_cases hia : i = a
      · rw [ite_eq_left hia, hia]
      · rw [ite_eq_right hia]
        exact he i (by omega))
    exact ⟨by rw [h.1]; omega, fun i hi => h.2 i (by omega)⟩

theorem hArr_size (q dn A : ℕ) : (hArr q dn A).size = A + 1 := by
  unfold hArr
  have h := hArr_go_spec q dn (A + 1) 0 (Array.emptyWithCapacity (A + 1)) (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  rw [h.1, Nat.zero_add]

theorem hArr_get (q dn A : ℕ) {i : ℕ} (hi : i ≤ A) : (hArr q dn A)[i]! = hUp q dn i := by
  unfold hArr
  have h := hArr_go_spec q dn (A + 1) 0 (Array.emptyWithCapacity (A + 1)) (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  exact h.2 i (by omega)

theorem weightByTau_go_spec (pm : Array ℕ) :
    ∀ (f a : ℕ) (acc : Array ℕ), acc.size = a → (∀ i < a, acc[i]! = (i + 1) * pm[i]!) →
      (weightByTau.go pm a f acc).size = a + f ∧
        ∀ i < a + f, (weightByTau.go pm a f acc)[i]! = (i + 1) * pm[i]! := by
  intro f
  induction f with
  | zero =>
    intro a acc hs he
    exact ⟨hs, fun i hi => he i (by omega)⟩
  | succ f ih =>
    intro a acc hs he
    rw [weightByTau.go.eq_2]
    have h := ih (a + 1) (acc.push ((a + 1) * pm[a]!)) (by rw [Array.size_push, hs])
      (fun i hi => by
        rw [aget_push, hs]
        by_cases hia : i = a
        · rw [ite_eq_left hia, hia]
        · rw [ite_eq_right hia]
          exact he i (by omega))
    exact ⟨by rw [h.1]; omega, fun i hi => h.2 i (by omega)⟩

theorem weightByTau_size (pm : Array ℕ) : (weightByTau pm).size = pm.size := by
  unfold weightByTau
  rw [(weightByTau_go_spec pm pm.size 0 _ (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))).1, Nat.zero_add]

theorem weightByTau_get (pm : Array ℕ) {i : ℕ} (hi : i < pm.size) :
    (weightByTau pm)[i]! = (i + 1) * pm[i]! := by
  unfold weightByTau
  exact (weightByTau_go_spec pm pm.size 0 _ (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))).2 i (by omega)

theorem weightByPow2_go_spec (pm : Array ℕ) :
    ∀ (f a : ℕ) (acc : Array ℕ), acc.size = a → (∀ i < a, acc[i]! = pm[i]! * 2 ^ i) →
      (weightByPow2.go pm a f acc).size = a + f ∧
        ∀ i < a + f, (weightByPow2.go pm a f acc)[i]! = pm[i]! * 2 ^ i := by
  intro f
  induction f with
  | zero =>
    intro a acc hs he
    exact ⟨hs, fun i hi => he i (by omega)⟩
  | succ f ih =>
    intro a acc hs he
    rw [weightByPow2.go.eq_2]
    have h := ih (a + 1) (acc.push (pm[a]! <<< a)) (by rw [Array.size_push, hs])
      (fun i hi => by
        rw [aget_push, hs]
        by_cases hia : i = a
        · rw [ite_eq_left hia, hia, Nat.shiftLeft_eq]
        · rw [ite_eq_right hia]
          exact he i (by omega))
    exact ⟨by rw [h.1]; omega, fun i hi => h.2 i (by omega)⟩

theorem weightByPow2_size (pm : Array ℕ) : (weightByPow2 pm).size = pm.size := by
  unfold weightByPow2
  rw [(weightByPow2_go_spec pm pm.size 0 _ (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))).1, Nat.zero_add]

theorem weightByPow2_get (pm : Array ℕ) {i : ℕ} (hi : i < pm.size) :
    (weightByPow2 pm)[i]! = pm[i]! * 2 ^ i := by
  unfold weightByPow2
  exact (weightByPow2_go_spec pm pm.size 0 _ (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))).2 i (by omega)

theorem acut60_go_le {q : ℕ} (hq : 2 ≤ q) :
    ∀ (f a : ℕ), q ^ a ≤ 2 ^ 60 → acut60.go q a (q ^ a) f ≤ 60 := by
  have key : ∀ a : ℕ, q ^ a ≤ 2 ^ 60 → a ≤ 60 := by
    intro a ha
    by_contra h
    have h1 : 2 ^ 61 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ a ≤ q ^ a := Nat.pow_le_pow_left hq a
    have h3 : (2 : ℕ) ^ 60 < 2 ^ 61 := by norm_num
    omega
  intro f
  induction f with
  | zero => intro a ha; exact key a ha
  | succ f ih =>
    intro a ha
    rw [acut60.go.eq_2]
    split_ifs with h
    · rw [← pow_succ]
      refine ih (a + 1) ?_
      rw [pow_succ, ← TWO60_eq]
      exact h
    · exact key a ha

/-- `acut60 q ≤ 60` for `q ≥ 2` (so `acut60 q < 64 ≤ N` for the caps of the τ_s and e laws). -/
theorem acut60_le {q : ℕ} (hq : 2 ≤ q) : acut60 q ≤ 60 := by
  unfold acut60
  have h := acut60_go_le hq 64 0 (by norm_num)
  simpa using h

/-! ### `lostSumW`, `prefixTables`, `suffixTablesW` -/

theorem lostSumW_go_eq (W : Array ℕ) (TM ac : ℕ) (hA : Array ℕ) :
    ∀ (f t acc : ℕ), lostSumW.go W TM ac hA t f acc =
      acc + ∑ t' ∈ Ico t (t + f), mulUp W[t']! hA[min (TM / t') (ac + 1)]! := by
  intro f
  induction f with
  | zero => intro t acc; simp [lostSumW.go]
  | succ f ih =>
    intro t acc
    rw [lostSumW.go.eq_2, sum_eq_sum_Ico_succ_bot (by omega : t < t + (f + 1))]
    split_ifs with h
    · have h0 : W[t]! = 0 := by simpa using h
      rw [ih, h0, mulUp_zero_left', show t + 1 + f = t + (f + 1) by omega]
      omega
    · rw [ih, show t + 1 + f = t + (f + 1) by omega]
      omega

/-- **`lostSumW`** as a finite sum: `Σ_{1 ≤ t ≤ TM} mulUp W[t] hA[min (TM/t) (ac+1)]`. -/
theorem lostSumW_eq (W : Array ℕ) (TM ac : ℕ) (hA : Array ℕ) :
    lostSumW W TM ac hA = ∑ t ∈ Ico 1 (TM + 1), mulUp W[t]! hA[min (TM / t) (ac + 1)]! := by
  unfold lostSumW
  rw [lostSumW_go_eq, Nat.zero_add, Nat.add_comm 1 TM]

/-- `S0[k] = Σ_{j ≤ k} D[j]`. -/
def pS0 (D : Array ℕ) (k : ℕ) : ℕ := ∑ j ∈ range (k + 1), D[j]!

/-- `S1[k] = Σ_{j ≤ k} j·D[j]`. -/
def pS1 (D : Array ℕ) (k : ℕ) : ℕ := ∑ j ∈ range (k + 1), j * D[j]!

theorem prefixTables_go_spec (D : Array ℕ) :
    ∀ (f j s0 s1 : ℕ) (S0 S1 : Array ℕ), S0.size = j → S1.size = j →
      s0 = ∑ i ∈ range j, D[i]! → s1 = ∑ i ∈ range j, i * D[i]! →
      (∀ i < j, S0[i]! = pS0 D i ∧ S1[i]! = pS1 D i) →
      (prefixTables.go D j s0 s1 S0 S1 f).1.size = j + f ∧
        (prefixTables.go D j s0 s1 S0 S1 f).2.size = j + f ∧
        ∀ i < j + f, (prefixTables.go D j s0 s1 S0 S1 f).1[i]! = pS0 D i ∧
          (prefixTables.go D j s0 s1 S0 S1 f).2[i]! = pS1 D i := by
  intro f
  induction f with
  | zero =>
    intro j s0 s1 S0 S1 hS hT _ _ he
    exact ⟨hS, hT, fun i hi => he i (by omega)⟩
  | succ f ih =>
    intro j s0 s1 S0 S1 hS hT hs0 hs1 he
    rw [prefixTables.go.eq_2]
    have e0 : s0 + D[j]! = pS0 D j := by rw [pS0, sum_range_succ, hs0]
    have e1 : s1 + j * D[j]! = pS1 D j := by rw [pS1, sum_range_succ, hs1]
    have h := ih (j + 1) (s0 + D[j]!) (s1 + j * D[j]!) (S0.push (s0 + D[j]!))
      (S1.push (s1 + j * D[j]!)) (by rw [Array.size_push, hS]) (by rw [Array.size_push, hT])
      (by rw [sum_range_succ, hs0]) (by rw [sum_range_succ, hs1])
      (fun i hi => by
        rw [aget_push, aget_push, hS, hT]
        by_cases hij : i = j
        · subst hij
          simp [e0, e1]
        · rw [ite_eq_right hij, ite_eq_right hij]
          exact he i (by omega))
    rw [show j + 1 + f = j + (f + 1) by omega] at h
    exact h

/-- **`prefixTables`**: sizes `D.size`, entries `S0[k] = Σ_{j ≤ k} D[j]`, `S1[k] = Σ_{j ≤ k} j·D[j]`. -/
theorem prefixTables_spec (D : Array ℕ) :
    (prefixTables D).1.size = D.size ∧ (prefixTables D).2.size = D.size ∧
      ∀ k < D.size, (prefixTables D).1[k]! = pS0 D k ∧ (prefixTables D).2[k]! = pS1 D k := by
  unfold prefixTables
  have h := prefixTables_go_spec D D.size 0 0 0 (Array.emptyWithCapacity D.size)
    (Array.emptyWithCapacity D.size) (by simp) (by simp) (by simp) (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  rw [Nat.zero_add] at h
  exact h

theorem suffixTablesW_go_spec (W : Array ℕ) (TS : ℕ) :
    ∀ (f aw av : ℕ) (SW SV : Array ℕ), f ≤ TS → SW.size = TS + 2 → SV.size = TS + 2 →
      aw = ∑ T ∈ Ioc f TS, W[T]! → av = ∑ T ∈ Ioc f TS, (W[T]! <<< 20) / T →
      (∀ k, SW[k]! = if f < k ∧ k ≤ TS then ∑ T ∈ Icc k TS, W[T]! else 0) →
      (∀ k, SV[k]! = if f < k ∧ k ≤ TS then ∑ T ∈ Icc k TS, (W[T]! <<< 20) / T else 0) →
      (suffixTablesW.go W f aw av SW SV f).1.size = TS + 2 ∧
        (suffixTablesW.go W f aw av SW SV f).2.size = TS + 2 ∧
        ∀ k, (suffixTablesW.go W f aw av SW SV f).1[k]! =
            (if 0 < k ∧ k ≤ TS then ∑ T ∈ Icc k TS, W[T]! else 0) ∧
          (suffixTablesW.go W f aw av SW SV f).2[k]! =
            (if 0 < k ∧ k ≤ TS then ∑ T ∈ Icc k TS, (W[T]! <<< 20) / T else 0) := by
  intro f
  induction f with
  | zero =>
    intro aw av SW SV _ hSW hSV _ _ he1 he2
    exact ⟨hSW, hSV, fun k => ⟨he1 k, he2 k⟩⟩
  | succ f ih =>
    intro aw av SW SV hf hSW hSV haw hav he1 he2
    rw [suffixTablesW.go.eq_2, show f + 1 - 1 = f by omega]
    have hI : Ioc f TS = insert (f + 1) (Ioc (f + 1) TS) := by
      ext x
      simp only [mem_Ioc, mem_insert]
      omega
    have hnot : f + 1 ∉ Ioc (f + 1) TS := by simp
    have hIcc : Icc (f + 1) TS = Ioc f TS := by
      ext x
      simp only [mem_Ioc, mem_Icc]
      omega
    refine ih (aw + W[f + 1]!) (av + (W[f + 1]! <<< 20) / (f + 1)) _ _ (by omega)
      (by rw [size_set, hSW]) (by rw [size_set, hSV])
      (by rw [hI, sum_insert hnot, haw]; omega) (by rw [hI, sum_insert hnot, hav]; omega)
      (fun k => ?_) (fun k => ?_)
    · rw [aget_set, hSW, he1]
      by_cases hk : f + 1 = k
      · subst hk
        rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left ⟨by omega, hf⟩, hIcc, hI, sum_insert hnot, haw]
        omega
      · rw [ite_eq_right (fun h => hk h.1)]
        by_cases hk2 : f + 1 < k ∧ k ≤ TS
        · rw [ite_eq_left hk2, ite_eq_left ⟨by omega, hk2.2⟩]
        · rw [ite_eq_right hk2, ite_eq_right (by omega)]
    · rw [aget_set, hSV, he2]
      by_cases hk : f + 1 = k
      · subst hk
        rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left ⟨by omega, hf⟩, hIcc, hI, sum_insert hnot, hav]
        omega
      · rw [ite_eq_right (fun h => hk h.1)]
        by_cases hk2 : f + 1 < k ∧ k ≤ TS
        · rw [ite_eq_left hk2, ite_eq_left ⟨by omega, hk2.2⟩]
        · rw [ite_eq_right hk2, ite_eq_right (by omega)]

/-- **`suffixTablesW`**: sizes `TS + 2`; for `1 ≤ k ≤ TS`, `SW[k] = Σ_{k ≤ T ≤ TS} W[T]` and
`SV[k] = Σ_{k ≤ T ≤ TS} ⌊W[T]·2^20/T⌋`; all other entries (`k = 0`, `k > TS`) are `0`. -/
theorem suffixTablesW_spec (W : Array ℕ) (TS : ℕ) :
    (suffixTablesW W TS).1.size = TS + 2 ∧ (suffixTablesW W TS).2.size = TS + 2 ∧
      ∀ k, (suffixTablesW W TS).1[k]! =
          (if 0 < k ∧ k ≤ TS then ∑ T ∈ Icc k TS, W[T]! else 0) ∧
        (suffixTablesW W TS).2[k]! =
          (if 0 < k ∧ k ≤ TS then ∑ T ∈ Icc k TS, (W[T]! <<< 20) / T else 0) := by
  unfold suffixTablesW
  refine suffixTablesW_go_spec W TS TS 0 0 _ _ le_rfl (size_zeros _) (size_zeros _)
    (by simp) (by simp) (fun k => ?_) (fun k => ?_)
  · rw [aget_zeros, ite_eq_right (by omega)]
  · rw [aget_zeros, ite_eq_right (by omega)]

/-! ### The e-law loops (`eInner`, `eOuter`, `ELaw.add`) -/

theorem eInner_spec (NN : ℕ) (mu : Array ℕ) (w e : ℕ) :
    ∀ (f a : ℕ) (Wn : Array ℕ) (Ls : ℕ), NN < Wn.size →
      (eInner NN mu w e a f (Wn, Ls)).1.size = Wn.size ∧
        (∀ j ≤ NN, (eInner NN mu w e a f (Wn, Ls)).1[j]! =
          Wn[j]! + ∑ a' ∈ Ico a (a + f), if e + a' = j then mulUp w mu[a']! else 0) ∧
        (eInner NN mu w e a f (Wn, Ls)).2 =
          Ls + ∑ a' ∈ Ico a (a + f), if NN < e + a' then mulUp w mu[a']! else 0 := by
  intro f
  induction f with
  | zero =>
    intro a Wn Ls _
    simp [eInner.eq_1]
  | succ f ih =>
    intro a Wn Ls hN
    have hsp : ∀ g : ℕ → ℕ, ∑ a' ∈ Ico a (a + (f + 1)), g a' =
        g a + ∑ a' ∈ Ico (a + 1) (a + 1 + f), g a' := fun g => by
      rw [sum_eq_sum_Ico_succ_bot (by omega : a < a + (f + 1)),
        show a + 1 + f = a + (f + 1) by omega]
    rw [eInner.eq_2]
    split_ifs with h
    · have h' := ih (a + 1) (Wn.set! (e + a) (Wn[e + a]! + mulUp w mu[a]!)) Ls
        (by rw [size_set]; exact hN)
      rw [size_set] at h'
      refine ⟨h'.1, fun j hj => ?_, ?_⟩
      · rw [h'.2.1 j hj, aget_set, hsp]
        by_cases hja : e + a = j
        · rw [ite_eq_left ⟨hja, by omega⟩, ite_eq_left hja, hja]
          omega
        · rw [ite_eq_right (fun h => hja h.1), ite_eq_right hja]
          omega
      · rw [h'.2.2, hsp, ite_eq_right (by omega)]
        omega
    · have h' := ih (a + 1) Wn (Ls + mulUp w mu[a]!) hN
      refine ⟨h'.1, fun j hj => ?_, ?_⟩
      · rw [h'.2.1 j hj, hsp, ite_eq_right (by omega)]
        omega
      · rw [h'.2.2, hsp, ite_eq_left (by omega)]
        omega

theorem eOuter_spec (NN : ℕ) (W mu : Array ℕ) (ac h2 : ℕ) :
    ∀ (f e : ℕ) (Wn : Array ℕ) (Ls : ℕ), NN < Wn.size →
      (eOuter NN W mu ac h2 e f (Wn, Ls)).1.size = Wn.size ∧
        (∀ j ≤ NN, (eOuter NN W mu ac h2 e f (Wn, Ls)).1[j]! =
          Wn[j]! + ∑ e' ∈ Ico e (e + f), ∑ a ∈ range (ac + 1),
            if e' + a = j then mulUp W[e']! mu[a]! else 0) ∧
        (eOuter NN W mu ac h2 e f (Wn, Ls)).2 =
          Ls + ∑ e' ∈ Ico e (e + f), ((∑ a ∈ range (ac + 1),
            if NN < e' + a then mulUp W[e']! mu[a]! else 0) + mulUp W[e']! h2) := by
  intro f
  induction f with
  | zero =>
    intro e Wn Ls _
    simp [eOuter.eq_1]
  | succ f ih =>
    intro e Wn Ls hN
    have hsp : ∀ g : ℕ → ℕ, ∑ e' ∈ Ico e (e + (f + 1)), g e' =
        g e + ∑ e' ∈ Ico (e + 1) (e + 1 + f), g e' := fun g => by
      rw [sum_eq_sum_Ico_succ_bot (by omega : e < e + (f + 1)),
        show e + 1 + f = e + (f + 1) by omega]
    rw [eOuter.eq_2]
    split_ifs with h
    · have h0 : W[e]! = 0 := by simpa using h
      have h' := ih (e + 1) Wn Ls hN
      refine ⟨h'.1, fun j hj => ?_, ?_⟩
      · rw [h'.2.1 j hj, hsp, h0]
        simp [mulUp_zero_left']
      · rw [h'.2.2, hsp, h0]
        simp [mulUp_zero_left']
    · have hI := eInner_spec NN mu W[e]! e (ac + 1) 0 Wn Ls hN
      rw [Nat.zero_add, ← range_eq_Ico] at hI
      rcases hE : eInner NN mu W[e]! e 0 (ac + 1) (Wn, Ls) with ⟨Wn', Ls'⟩
      rw [hE] at hI
      simp only at hI
      have h' := ih (e + 1) Wn' (Ls' + mulUp W[e]! h2) (by rw [hI.1]; exact hN)
      refine ⟨by rw [h'.1, hI.1], fun j hj => ?_, ?_⟩
      · rw [h'.2.1 j hj, hI.2.1 j hj, hsp]
        omega
      · rw [h'.2.2, hI.2.2, hsp]
        omega

/-- `ELaw.add`, the new weighted law: for `j ≤ NN`,
`W'[j] = Σ_{e ≤ NN} Σ_{a ≤ ac} [e + a = j] mulUp W[e] mu[a]`, `mu = weightByPow2 (pmArr q dn ac)`. -/
theorem eLawAdd_W (st : ELaw) (NN q dn : ℕ) :
    (st.add NN q dn).W.size = NN + 1 ∧
      ∀ j ≤ NN, (st.add NN q dn).W[j]! =
        ∑ e ∈ range (NN + 1), ∑ a ∈ range (acut60 q + 1),
          if e + a = j then mulUp st.W[e]! (weightByPow2 (pmArr q dn (acut60 q)))[a]! else 0 := by
  have h := eOuter_spec NN st.W (weightByPow2 (pmArr q dn (acut60 q))) (acut60 q)
    (h2Up q dn (acut60 q + 1)) (NN + 1) 0 (zeros (NN + 1)) 0 (by rw [size_zeros]; omega)
  rw [Nat.zero_add, ← range_eq_Ico] at h
  unfold ELaw.add
  dsimp only
  rcases hE : eOuter NN st.W (weightByPow2 (pmArr q dn (acut60 q))) (acut60 q)
    (h2Up q dn (acut60 q + 1)) 0 (NN + 1) (zeros (NN + 1), 0) with ⟨Wn, Ls⟩
  rw [hE] at h
  simp only at h ⊢
  refine ⟨by rw [h.1, size_zeros], fun j hj => ?_⟩
  rw [h.2.1 j hj, aget_zeros, Nat.zero_add]

/-- `ELaw.add`, the new lost mass:
`lost' = mulUp lost (e2Up q dn) + Σ_{e ≤ NN} (Σ_{a ≤ ac, NN < e + a} mulUp W[e] mu[a] + mulUp W[e] h2)`. -/
theorem eLawAdd_lost (st : ELaw) (NN q dn : ℕ) :
    (st.add NN q dn).lost = mulUp st.lost (e2Up q dn) +
      ∑ e ∈ range (NN + 1), ((∑ a ∈ range (acut60 q + 1),
        if NN < e + a then mulUp st.W[e]! (weightByPow2 (pmArr q dn (acut60 q)))[a]! else 0) +
        mulUp st.W[e]! (h2Up q dn (acut60 q + 1))) := by
  have h := eOuter_spec NN st.W (weightByPow2 (pmArr q dn (acut60 q))) (acut60 q)
    (h2Up q dn (acut60 q + 1)) (NN + 1) 0 (zeros (NN + 1)) 0 (by rw [size_zeros]; omega)
  rw [Nat.zero_add, ← range_eq_Ico] at h
  unfold ELaw.add
  dsimp only
  rcases hE : eOuter NN st.W (weightByPow2 (pmArr q dn (acut60 q))) (acut60 q)
    (h2Up q dn (acut60 q + 1)) 0 (NN + 1) (zeros (NN + 1), 0) with ⟨Wn, Ls⟩
  rw [hE] at h
  simp only at h ⊢
  rw [h.2.2, Nat.zero_add]

/-! ### The S/B/H tables: `ebLoW`, `rowsStep` -/

theorem ebLoW_go_eq (a Bq Bdn : Array ℕ) :
    ∀ (f i acc : ℕ), ebLoW.go a Bq Bdn i f acc =
      acc + ∑ i' ∈ Ico i (i + f), a[i']! * (DDEN * W48 / (nuDen Bdn[i']! * Bq[i']!)) := by
  intro f
  induction f with
  | zero => intro i acc; simp [ebLoW.go]
  | succ f ih =>
    intro i acc
    rw [ebLoW.go.eq_2, ih, sum_eq_sum_Ico_succ_bot (by omega : i < i + (f + 1)),
      show i + 1 + f = i + (f + 1) by omega]
    omega

/-- **`ebLoW`** as a finite sum: `Σ_{i < a.size} a[i]·⌊10^9·2^48/(nd_i q_i)⌋`. -/
theorem ebLoW_eq (a Bq Bdn : Array ℕ) :
    ebLoW a Bq Bdn = ∑ i ∈ range a.size, a[i]! * (DDEN * W48 / (nuDen Bdn[i]! * Bq[i]!)) := by
  unfold ebLoW
  rw [ebLoW_go_eq, Nat.zero_add, Nat.zero_add, range_eq_Ico]

/-- One new row of `rowsStep` (row `b`): `base = dpRange 0 rows[b] K pm 0 1` (exponent `0`), plus
`dpRange base rows[b − s] K pm 1 K` (exponents `1 ≤ a < K`, increment `s` of `b`) when `s ≤ b`. -/
def rowNew (rows : Array (Array ℕ)) (K s : ℕ) (pm : Array ℕ) (b : ℕ) : Array ℕ :=
  if s ≤ b then dpRange (dpRange (zeros (K + 1)) rows[b]! K pm 0 1) rows[b - s]! K pm 1 K
  else dpRange (zeros (K + 1)) rows[b]! K pm 0 1

theorem rowsStep_go_spec (rows : Array (Array ℕ)) (K s : ℕ) (pm : Array ℕ) :
    ∀ (f b : ℕ) (acc : Array (Array ℕ)), acc.size = b →
      (∀ b' < b, acc[b']! = rowNew rows K s pm b') →
      (rowsStep.go rows K s pm b f acc).size = b + f ∧
        ∀ b' < b + f, (rowsStep.go rows K s pm b f acc)[b']! = rowNew rows K s pm b' := by
  intro f
  induction f with
  | zero =>
    intro b acc hs he
    exact ⟨hs, fun i hi => he i (by omega)⟩
  | succ f ih =>
    intro b acc hs he
    have e : rowsStep.go rows K s pm b (f + 1) acc =
        rowsStep.go rows K s pm (b + 1) f (acc.push (rowNew rows K s pm b)) :=
      rowsStep.go.eq_2 rows K s pm b acc f
    rw [e]
    have h := ih (b + 1) (acc.push (rowNew rows K s pm b)) (by rw [Array.size_push, hs])
      (fun i hi => by
        rw [aget_push, hs]
        by_cases hib : i = b
        · rw [ite_eq_left hib, hib]
        · rw [ite_eq_right hib]
          exact he i (by omega))
    exact ⟨by rw [h.1]; omega, fun i hi => h.2 i (by omega)⟩

theorem rowsStep_size (rows : Array (Array ℕ)) (K s : ℕ) (pm : Array ℕ) :
    (rowsStep rows K s pm).size = rows.size := by
  unfold rowsStep
  rw [(rowsStep_go_spec rows K s pm rows.size 0 _ (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))).1, Nat.zero_add]

theorem rowsStep_get (rows : Array (Array ℕ)) (K s : ℕ) (pm : Array ℕ) {b : ℕ}
    (hb : b < rows.size) : (rowsStep rows K s pm)[b]! = rowNew rows K s pm b := by
  unfold rowsStep
  exact (rowsStep_go_spec rows K s pm rows.size 0 _ (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i))).2 b (by omega)

theorem rowNew_size (rows : Array (Array ℕ)) (K s : ℕ) (pm : Array ℕ) (b : ℕ) :
    (rowNew rows K s pm b).size = K + 1 := by
  unfold rowNew
  split_ifs <;> simp only [dpRange_size, size_zeros]

/-- **The entries of a new row**: for `T ≤ K`,
`new[b][T] = Σ_{1 ≤ t ≤ K} [t = T] mulUp rows[b][t] pm[0]
  + [s ≤ b] Σ_{1 ≤ t ≤ K} Σ_{1 ≤ a < K} [t (a+1) = T] mulUp rows[b − s][t] pm[a]`. -/
theorem rowNew_get (rows : Array (Array ℕ)) (K s : ℕ) (pm : Array ℕ) (b : ℕ) {T : ℕ}
    (hT : T ≤ K) :
    (rowNew rows K s pm b)[T]! =
      (∑ t ∈ Ico 1 (K + 1), if t = T then mulUp rows[b]![t]! pm[0]! else 0) +
        if s ≤ b then ∑ t ∈ Ico 1 (K + 1), ∑ a ∈ Ico 1 K,
          (if t * (a + 1) = T then mulUp rows[b - s]![t]! pm[a]! else 0) else 0 := by
  have hbase : (dpRange (zeros (K + 1)) rows[b]! K pm 0 1)[T]! =
      ∑ t ∈ Ico 1 (K + 1), if t = T then mulUp rows[b]![t]! pm[0]! else 0 := by
    rw [dpRange_zeros_get _ K pm 0 1 hT]
    refine sum_congr rfl fun t _ => ?_
    rw [show Ico 0 1 = {0} from rfl, sum_singleton, Nat.zero_add, Nat.mul_one]
  unfold rowNew
  split_ifs with hs
  · rw [dpRange_get _ _ K pm 1 K (by rw [dpRange_zeros_size]; omega) hT, hbase]
  · rw [hbase]
    exact (Nat.add_zero _).symm

end MinModulus.Checker2Sound.C
