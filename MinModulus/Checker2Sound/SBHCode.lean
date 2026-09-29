import MinModulus.Checker2Sound.Defs
import MinModulus.CheckerSound.Sieve

/-!
# `Checker2Sound.SBHCode` (agent L2-D): natural-number semantics of the S/B/H code

STATUS: complete (fully proved; agent L2-D). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Facts about the code of `Checker2Impl/SBH.lean` (namespace `MinModulus.Checker2Sound.D`):
* array access (`getElem!_*`), the prime array (`primes2_*`: increasing, prime, `≤ PX`,
  complete), `idxSet` (`mem_idxSet`, `idxSet_union`, `idxSet_disjoint`, `idxSet_insert`,
  `primesBelow_eq_idxSet`), `countLt` (`lt_of_lt_countLt`, `le_of_countLt_le`);
* the S/B/H index split `sbh_split` (`S = [0, iS)`, `B = [iS, iB)`, `H = [iB, k)`), `lt_cdiv_iff`;
* `j0m1_le` (`j0m1 ≤ j0 − 1`), `cdTable_size`/`cdTable_get`, `kkOf_le`/`le_pow_kkOf`,
  `strides_spec` (mixed-radix strides `sprod`);
* **`smallDivs_spec`**: at the pattern index `Σ_i e i · stride i` (digits `e i ≤ kk[i]`, distinct
  primes), `smallDivs` lists the divisors below `N1` of `∏_i Sq[i]^{e i}`, without repetition;
* `sumCd_eq`, `profileOf_get` (counts), **`patternData_spec`** (`findIdx?` deduplication: each
  pattern's `patF` and profile table are the right ones), **`corrSum_spec`** (the guard
  `⌊c_b⌋ ≤ K` and the exact sum of the row terms `corrTerm`);
* the DFS: `dfs_ok_mono` (`ok` only goes from `true` to `false`) and the abstract soundness
  theorem **`dfs_sound`** (induction on the fuel of `dfsNode`/`dfsExp` against any node value
  `V`, invariant `I`, leaf/split/prune hypotheses);
* P- and W-value rounding (`pv_mul_le_mulUp'`, `pv_mul_wv_le_mulUp`, `wv_sub_ge`, …).
-/

namespace MinModulus.Checker2Sound.D

open MinModulus.CheckerImpl MinModulus.Checker2Impl Finset

/-! ### Array access -/

theorem getElem!_eq_getD' {α : Type*} [Inhabited α] (xs : Array α) (i : ℕ) :
    xs[i]! = xs[i]?.getD default := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem getElem!_of_lt {α : Type*} [Inhabited α] (xs : Array α) {i : ℕ} (h : i < xs.size) :
    xs[i]! = xs[i] := by
  rw [getElem!_eq_getD', Array.getElem?_eq_getElem h]
  rfl

theorem getElem!_of_size_le' {α : Type*} [Inhabited α] (xs : Array α) {i : ℕ}
    (h : xs.size ≤ i) : xs[i]! = default := by
  rw [getElem!_eq_getD', Array.getElem?_eq_none h]
  rfl

theorem getElem!_extract {α : Type*} [Inhabited α] (xs : Array α) {s e i : ℕ}
    (h : i < min e xs.size - s) : (xs.extract s e)[i]! = xs[s + i]! := by
  rw [getElem!_eq_getD', getElem!_eq_getD', Array.getElem?_extract, ite_eq_left h]

theorem size_extract' {α : Type*} (xs : Array α) (s e : ℕ) :
    (xs.extract s e).size = min e xs.size - s := Array.size_extract

theorem getElem!_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (xs : Array α)
    {i : ℕ} (h : i < xs.size) : (xs.map f)[i]! = f xs[i]! := by
  rw [getElem!_eq_getD', getElem!_eq_getD', Array.getElem?_map, Array.getElem?_eq_getElem h]
  rfl

theorem getElem!_range_map {β : Type*} [Inhabited β] (f : ℕ → β) {n i : ℕ} (h : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_map f _ (by simpa using h), getElem!_eq_getD', Array.getElem?_range, ite_eq_left h]
  rfl

theorem getElem!_push' {α : Type*} [Inhabited α] (xs : Array α) (x : α) (j : ℕ) :
    (xs.push x)[j]! = if j = xs.size then x else xs[j]! := by
  rw [getElem!_eq_getD', getElem!_eq_getD', Array.getElem?_push]
  split_ifs <;> rfl

theorem getElem!_push_lt {α : Type*} [Inhabited α] (xs : Array α) (x : α) {j : ℕ}
    (h : j < xs.size) : (xs.push x)[j]! = xs[j]! := by
  rw [getElem!_push', ite_eq_right (by omega)]

theorem getElem!_push_size {α : Type*} [Inhabited α] (xs : Array α) (x : α) :
    (xs.push x)[xs.size]! = x := by
  rw [getElem!_push', ite_eq_left rfl]

theorem getElem!_push_of_eq {α : Type*} [Inhabited α] (xs : Array α) (x : α) {j : ℕ}
    (h : xs.size = j) : (xs.push x)[j]! = x := by
  rw [← h]; exact getElem!_push_size xs x

theorem getElem!_toList_eq {α : Type*} [Inhabited α] (xs : Array α) (i : ℕ) :
    xs.toList[i]! = xs[i]! := Array.getElem!_toList

theorem getElem_toList_eq_getElem! {α : Type*} [Inhabited α] (xs : Array α) {i : ℕ}
    (h : i < xs.toList.length) : xs.toList[i] = xs[i]! := by
  rw [getElem!_of_lt xs (by simpa using h)]
  simp

theorem mem_toList_iff_getElem! {α : Type*} [Inhabited α] (xs : Array α) (x : α) :
    x ∈ xs.toList ↔ ∃ i, i < xs.size ∧ xs[i]! = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by simpa using hi, (getElem_toList_eq_getElem! xs hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by simpa using hi, getElem_toList_eq_getElem! xs (by simpa using hi)⟩

/-! ### The prime array `primes2 P` -/

section Primes

variable (P : Params2)

theorem primes2_toList :
    (primes2 P).toList = (List.range (P.PX + 1)).filter (fun k => decide k.Prime) :=
  MinModulus.CheckerSound.A.primesUpTo_toList P.PX

theorem primes2_pairwise : (primes2 P).toList.Pairwise (· < ·) :=
  MinModulus.CheckerSound.A.primesUpTo_pairwise P.PX

theorem primes2_nodup : (primes2 P).toList.Nodup :=
  MinModulus.CheckerSound.A.primesUpTo_nodup P.PX

theorem mem_primes2 {n : ℕ} : n ∈ (primes2 P).toList ↔ n.Prime ∧ n ≤ P.PX :=
  MinModulus.CheckerSound.A.mem_primesUpTo

variable {P}

theorem primes2_get_mem {i : ℕ} (hi : i < (primes2 P).size) :
    (primes2 P)[i]! ∈ (primes2 P).toList :=
  (mem_toList_iff_getElem! _ _).2 ⟨i, hi, rfl⟩

theorem primes2_prime {i : ℕ} (hi : i < (primes2 P).size) : ((primes2 P)[i]!).Prime :=
  ((mem_primes2 P).1 (primes2_get_mem hi)).1

theorem primes2_le {i : ℕ} (hi : i < (primes2 P).size) : (primes2 P)[i]! ≤ P.PX :=
  ((mem_primes2 P).1 (primes2_get_mem hi)).2

theorem primes2_lt_of_lt {i j : ℕ} (hij : i < j) (hj : j < (primes2 P).size) :
    (primes2 P)[i]! < (primes2 P)[j]! := by
  have hp := primes2_pairwise P
  rw [List.pairwise_iff_getElem] at hp
  have h := hp i j (by simp; omega) (by simpa using hj) hij
  rwa [getElem_toList_eq_getElem!, getElem_toList_eq_getElem!] at h

theorem primes2_le_of_le {i j : ℕ} (hij : i ≤ j) (hj : j < (primes2 P).size) :
    (primes2 P)[i]! ≤ (primes2 P)[j]! := by
  rcases Nat.eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (primes2_lt_of_lt h hj).le

theorem primes2_inj {i j : ℕ} (hi : i < (primes2 P).size) (hj : j < (primes2 P).size)
    (h : (primes2 P)[i]! = (primes2 P)[j]!) : i = j := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h (primes2_lt_of_lt hij hj).ne
  · rfl
  · exact absurd h (primes2_lt_of_lt hij hi).ne'

theorem primes2_index_of_prime {q : ℕ} (hq : q.Prime) (hqPX : q ≤ P.PX) :
    ∃ i, i < (primes2 P).size ∧ (primes2 P)[i]! = q :=
  (mem_toList_iff_getElem! _ _).1 ((mem_primes2 P).2 ⟨hq, hqPX⟩)

theorem two_le_primes2 {i : ℕ} (hi : i < (primes2 P).size) : 2 ≤ (primes2 P)[i]! :=
  (primes2_prime hi).two_le

/-! ### `idxSet` -/

theorem mem_idxSet {lo hi q : ℕ} :
    q ∈ idxSet P lo hi ↔ ∃ i, lo ≤ i ∧ i < hi ∧ i < (primes2 P).size ∧ (primes2 P)[i]! = q := by
  unfold idxSet
  rw [List.mem_toFinset, List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_take, List.length_drop, Array.length_toList] at hj
    refine ⟨lo + j, by omega, by omega, by omega, ?_⟩
    simp only [List.getElem_take, List.getElem_drop]
    rw [getElem_toList_eq_getElem!]
  · rintro ⟨i, h1, h2, h3, rfl⟩
    refine ⟨i - lo, by simp; omega, ?_⟩
    simp only [List.getElem_take, List.getElem_drop]
    rw [getElem_toList_eq_getElem!]
    congr 1
    omega

theorem idxSet_prime {lo hi q : ℕ} (hq : q ∈ idxSet P lo hi) : q.Prime := by
  obtain ⟨i, -, -, hi, rfl⟩ := mem_idxSet.1 hq
  exact primes2_prime hi

theorem idxSet_le_PX {lo hi q : ℕ} (hq : q ∈ idxSet P lo hi) : q ≤ P.PX := by
  obtain ⟨i, -, -, hi, rfl⟩ := mem_idxSet.1 hq
  exact primes2_le hi

theorem idxSet_union {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    idxSet P a c = idxSet P a b ∪ idxSet P b c := by
  ext q
  simp only [mem_union, mem_idxSet]
  constructor
  · rintro ⟨i, h1, h2, h3, h4⟩
    by_cases hib : i < b
    · exact Or.inl ⟨i, h1, hib, h3, h4⟩
    · exact Or.inr ⟨i, by omega, h2, h3, h4⟩
  · rintro (⟨i, h1, h2, h3, h4⟩ | ⟨i, h1, h2, h3, h4⟩)
    · exact ⟨i, h1, by omega, h3, h4⟩
    · exact ⟨i, by omega, h2, h3, h4⟩

theorem idxSet_disjoint {a b c d : ℕ} (h : b ≤ c) : Disjoint (idxSet P a b) (idxSet P c d) := by
  rw [Finset.disjoint_left]
  intro q hq1 hq2
  obtain ⟨i, -, hib, hi, rfl⟩ := mem_idxSet.1 hq1
  obtain ⟨j, hcj, -, hj, hij⟩ := mem_idxSet.1 hq2
  have := primes2_inj hj hi hij
  omega

theorem idxSet_empty {a b : ℕ} (h : b ≤ a) : idxSet P a b = ∅ := by
  ext q
  simp only [mem_idxSet, Finset.notMem_empty, iff_false]
  rintro ⟨i, h1, h2, -, -⟩
  omega

theorem idxSet_insert {a b : ℕ} (hab : a < b) (hb : b ≤ (primes2 P).size) :
    idxSet P a b = insert ((primes2 P)[a]!) (idxSet P (a + 1) b) := by
  ext q
  simp only [mem_insert, mem_idxSet]
  constructor
  · rintro ⟨i, h1, h2, h3, rfl⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ⟨i, h, h2, h3, rfl⟩
  · rintro (rfl | ⟨i, h1, h2, h3, rfl⟩)
    · exact ⟨a, le_rfl, hab, by omega, rfl⟩
    · exact ⟨i, by omega, h2, h3, rfl⟩

theorem notMem_idxSet_succ {a b : ℕ} (ha : a < (primes2 P).size) :
    (primes2 P)[a]! ∉ idxSet P (a + 1) b := by
  intro h
  obtain ⟨i, h1, -, hi, hia⟩ := mem_idxSet.1 h
  have := primes2_inj hi ha hia
  omega

/-- The primes below `p = primes[k]` are the first `k` entries. -/
theorem primesBelow_eq_idxSet {k : ℕ} (hk : k < (primes2 P).size) :
    Nat.primesBelow ((primes2 P)[k]!) = idxSet P 0 k := by
  ext q
  rw [Nat.mem_primesBelow, mem_idxSet]
  constructor
  · rintro ⟨hqp, hq⟩
    have hqPX : q ≤ P.PX := (le_of_lt hqp).trans (primes2_le hk)
    obtain ⟨i, hi, rfl⟩ := primes2_index_of_prime hq hqPX
    refine ⟨i, Nat.zero_le i, ?_, hi, rfl⟩
    by_contra hik
    exact absurd hqp (not_lt.2 (primes2_le_of_le (not_lt.1 hik) hi))
  · rintro ⟨i, -, hik, hi, rfl⟩
    exact ⟨primes2_lt_of_lt hik hk, primes2_prime hi⟩

theorem extract_toList_toFinset (a b : ℕ) :
    ((primes2 P).extract a b).toList.toFinset = idxSet P a b := by
  unfold idxSet
  rw [Array.toList_extract, List.extract_eq_take_drop]

end Primes

/-! ### `countLt` -/

theorem countLt_go_spec (ps : Array ℕ) (v : ℕ) :
    ∀ f i, i + f = ps.size →
      i ≤ countLt.go ps v i f ∧ countLt.go ps v i f ≤ ps.size ∧
      (∀ j, i ≤ j → j < countLt.go ps v i f → ps[j]! < v) ∧
      (countLt.go ps v i f < ps.size → v ≤ ps[countLt.go ps v i f]!) := by
  intro f
  induction f with
  | zero =>
    intro i hi
    simp only [countLt.go]
    refine ⟨le_rfl, by omega, fun j h1 h2 => by omega, fun h => by omega⟩
  | succ f ih =>
    intro i hi
    simp only [countLt.go]
    split_ifs with h
    · obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (by omega)
      refine ⟨by omega, h2, fun j hj1 hj2 => ?_, h4⟩
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hj
      · exact h
      · exact h3 j hj hj2
    · refine ⟨le_rfl, by omega, fun j h1 h2 => by omega, fun _ => by omega⟩

theorem countLt_le_size (ps : Array ℕ) (v : ℕ) : countLt ps v ≤ ps.size :=
  (countLt_go_spec ps v ps.size 0 (by omega)).2.1

theorem lt_of_lt_countLt (ps : Array ℕ) (v : ℕ) {j : ℕ} (hj : j < countLt ps v) : ps[j]! < v :=
  (countLt_go_spec ps v ps.size 0 (by omega)).2.2.1 j (Nat.zero_le j) hj

theorem le_get_countLt (ps : Array ℕ) (v : ℕ) (h : countLt ps v < ps.size) :
    v ≤ ps[countLt ps v]! :=
  (countLt_go_spec ps v ps.size 0 (by omega)).2.2.2 h

/-- For the (increasing) prime array: every entry at index `≥ countLt primes v` is `≥ v`. -/
theorem le_of_countLt_le {P : Params2} (v : ℕ) {j : ℕ} (hj : countLt (primes2 P) v ≤ j)
    (hjs : j < (primes2 P).size) : v ≤ (primes2 P)[j]! :=
  (le_get_countLt _ v (lt_of_le_of_lt hj hjs)).trans (primes2_le_of_le hj hjs)


/-! ### `cdiv` thresholds -/

theorem lt_cdiv_iff {a m b : ℕ} (hb : 0 < b) : a < cdiv m b ↔ a * b < m := by
  unfold cdiv
  rw [← Nat.succ_le_iff, Nat.le_div_iff_mul_le hb, Nat.succ_mul]
  omega

theorem le_cdiv_mul (m b : ℕ) (hb : 0 < b) : m ≤ cdiv m b * b := cdiv_spec hb

/-! ### The S/B/H index split -/

section Split

variable {P : Params2}

/-- The index split of `sbhCost`: `S = [0, iS)`, `B = [iS, iB)`, `H = [iB, k)`. -/
theorem sbh_split {k : ℕ} (hk : k < (primes2 P).size) (y N1 : ℕ) :
    min (countLt (primes2 P) y) k ≤ max (min (countLt (primes2 P) y) k)
        (min (countLt (primes2 P) N1) k) ∧
      max (min (countLt (primes2 P) y) k) (min (countLt (primes2 P) N1) k) ≤ k ∧
      (∀ i, i < min (countLt (primes2 P) y) k → (primes2 P)[i]! < y) ∧
      (∀ i, min (countLt (primes2 P) y) k ≤ i →
        i < max (min (countLt (primes2 P) y) k) (min (countLt (primes2 P) N1) k) →
          y ≤ (primes2 P)[i]! ∧ (primes2 P)[i]! < N1) ∧
      (∀ i, max (min (countLt (primes2 P) y) k) (min (countLt (primes2 P) N1) k) ≤ i → i < k →
        N1 ≤ (primes2 P)[i]!) := by
  refine ⟨le_max_left _ _, max_le (min_le_right _ _) (min_le_right _ _), ?_, ?_, ?_⟩
  · intro i hi
    exact lt_of_lt_countLt _ _ (lt_of_lt_of_le hi (min_le_left _ _))
  · intro i h1 h2
    have hik : i < k := lt_of_lt_of_le h2 (max_le (min_le_right _ _) (min_le_right _ _))
    have h2' : i < min (countLt (primes2 P) N1) k := by
      rcases le_total (min (countLt (primes2 P) y) k) (min (countLt (primes2 P) N1) k) with h | h
      · rw [max_eq_right h] at h2; exact h2
      · rw [max_eq_left h] at h2; omega
    refine ⟨?_, lt_of_lt_countLt _ _ (lt_of_lt_of_le h2' (min_le_left _ _))⟩
    have : countLt (primes2 P) y ≤ i := by
      rcases le_total (countLt (primes2 P) y) k with h | h
      · rw [min_eq_left h] at h1; exact h1
      · rw [min_eq_right h] at h1; omega
    exact le_of_countLt_le y this (by omega)
  · intro i h1 h2
    have : countLt (primes2 P) N1 ≤ i := by
      have h3 := le_trans (le_max_right _ _) h1
      rcases le_total (countLt (primes2 P) N1) k with h | h
      · rw [min_eq_left h] at h3; exact h3
      · rw [min_eq_right h] at h3; omega
    exact le_of_countLt_le N1 this (by omega)

end Split

/-! ### `j0m1`, `cdLoW`, `cdTable` -/

theorem j0m1_go_le {m p d : ℕ} (hp : 1 < p) (hd : 0 < d) :
    ∀ f j x, x = d * p ^ (j + 1) → j ≤ MinModulus.Smooth.j0 p m d - 1 →
      j0m1.go m p x j f ≤ MinModulus.Smooth.j0 p m d - 1 := by
  intro f
  induction f with
  | zero => intro j x _ hj; simpa [j0m1.go] using hj
  | succ f ih =>
    intro j x hx hj
    simp only [j0m1.go]
    split_ifs with h
    · apply ih (j + 1) (x * p) (by rw [hx]; ring)
      have := (MinModulus.Smooth.lt_j0_iff (m := m) hp hd (Nat.succ_pos j)).2 (by rw [← hx]; exact h)
      omega
    · exact hj

theorem j0m1_le {m p d : ℕ} (hp : 1 < p) (hd : 0 < d) :
    j0m1 m p d ≤ MinModulus.Smooth.j0 p m d - 1 :=
  j0m1_go_le hp hd 64 0 (d * p) (by ring) (Nat.zero_le _)

theorem cdTable_go_spec (m p : ℕ) :
    ∀ f d (acc : Array ℕ), acc.size = d →
      (cdTable.go m p d f acc).size = d + f ∧
      ∀ i, i < d + f → (cdTable.go m p d f acc)[i]! = if i < d then acc[i]! else cdLoW m p i := by
  intro f
  induction f with
  | zero =>
    intro d acc hacc
    refine ⟨by simp [cdTable.go, hacc], fun i hi => ?_⟩
    simp only [cdTable.go]
    rw [ite_eq_left (by omega)]
  | succ f ih =>
    intro d acc hacc
    simp only [cdTable.go]
    obtain ⟨h1, h2⟩ := ih (d + 1) (acc.push (cdLoW m p d)) (by simp [hacc])
    refine ⟨by rw [h1]; ring, fun i hi => ?_⟩
    rw [h2 i (by omega)]
    by_cases hid : i < d
    · rw [ite_eq_left (by omega), ite_eq_left hid, getElem!_push_lt _ _ (by omega)]
    · by_cases hid' : i = d
      · subst hid'
        rw [ite_eq_left (by omega), ite_eq_right hid, ← hacc, getElem!_push_size]
      · rw [ite_eq_right (by omega), ite_eq_right hid]

theorem cdTable_size (m p N1 : ℕ) : (cdTable m p N1).size = N1 := by
  have := (cdTable_go_spec m p N1 0 (Array.emptyWithCapacity N1) (by simp)).1
  simpa [cdTable] using this

theorem cdTable_get (m p N1 : ℕ) {d : ℕ} (hd : d < N1) : (cdTable m p N1)[d]! = cdLoW m p d := by
  have := (cdTable_go_spec m p N1 0 (Array.emptyWithCapacity N1) (by simp)).2 d (by omega)
  simpa [cdTable] using this


/-! ### `kkOf` -/

theorem kkOf_go_spec {q N1 : ℕ} :
    ∀ f k qk, qk = q ^ (k + 1) →
      kkOf.go q N1 k qk f ≤ k + f ∧
        (kkOf.go q N1 k qk f < k + f → N1 ≤ q ^ (kkOf.go q N1 k qk f + 1)) := by
  intro f
  induction f with
  | zero => intro k qk _; simp [kkOf.go]
  | succ f ih =>
    intro k qk hqk
    simp only [kkOf.go]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := ih (k + 1) (qk * q) (by rw [hqk]; ring)
      exact ⟨by omega, fun h3 => h2 (by omega)⟩
    · exact ⟨by omega, fun _ => by rw [← hqk]; omega⟩

theorem kkOf_le (q N1 : ℕ) : kkOf q N1 ≤ 64 := by
  have := (kkOf_go_spec (q := q) (N1 := N1) 64 0 q (by ring)).1
  simpa [kkOf] using this

theorem le_pow_kkOf {q N1 : ℕ} (h : kkOf q N1 < 64) : N1 ≤ q ^ (kkOf q N1 + 1) :=
  (kkOf_go_spec (q := q) (N1 := N1) 64 0 q (by ring)).2 (by simpa [kkOf] using h)

/-! ### `strides` -/

/-- `∏_{l < i} (kk[l] + 1)`: the mixed-radix stride of digit `i`. -/
def sprod (kk : Array ℕ) (i : ℕ) : ℕ := ∏ l ∈ range i, (kk[l]! + 1)

theorem strides_aux (L : List ℕ) :
    ∀ (A : Array ℕ) (c : ℕ),
      (L.foldl (fun (acc : Array ℕ × ℕ) k => (acc.1.push acc.2, acc.2 * (k + 1))) (A, c)).1.size =
          A.size + L.length ∧
      (L.foldl (fun (acc : Array ℕ × ℕ) k => (acc.1.push acc.2, acc.2 * (k + 1))) (A, c)).2 =
          c * ∏ l ∈ range L.length, (L[l]! + 1) ∧
      ∀ i, i < A.size + L.length →
        (L.foldl (fun (acc : Array ℕ × ℕ) k => (acc.1.push acc.2, acc.2 * (k + 1))) (A, c)).1[i]! =
          if i < A.size then A[i]! else c * ∏ l ∈ range (i - A.size), (L[l]! + 1) := by
  induction L with
  | nil =>
    intro A c
    refine ⟨by simp, by simp, fun i hi => ?_⟩
    simp only [List.length_nil, add_zero] at hi
    simp [hi]
  | cons x L ih =>
    intro A c
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (A.push c) (c * (x + 1))
    refine ⟨by rw [h1, Array.size_push]; simp; ring, ?_, fun i hi => ?_⟩
    · rw [h2, List.length_cons, prod_range_succ']
      simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
      ring
    · rw [h3 i (by rw [Array.size_push]; simp at hi; omega)]
      rw [Array.size_push]
      by_cases hiA : i < A.size
      · rw [ite_eq_left (by omega), ite_eq_left hiA, getElem!_push_lt _ _ hiA]
      · by_cases hiA' : i = A.size
        · subst hiA'
          rw [ite_eq_left (by omega), ite_eq_right hiA, getElem!_push_size]
          simp
        · rw [ite_eq_right (by omega), ite_eq_right hiA]
          have e : i - A.size = (i - (A.size + 1)) + 1 := by omega
          rw [e, prod_range_succ']
          simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
          ring

theorem strides_spec (kk : Array ℕ) :
    (strides kk).1.size = kk.size ∧ (strides kk).2 = sprod kk kk.size ∧
      ∀ i, i < kk.size → (strides kk).1[i]! = sprod kk i := by
  have hs : strides kk = kk.toList.foldl
      (fun (acc : Array ℕ × ℕ) k => (acc.1.push acc.2, acc.2 * (k + 1))) (#[], 1) := by
    rw [strides, Array.foldl_toList]
  obtain ⟨h1, h2, h3⟩ := strides_aux kk.toList #[] 1
  have hl : ∀ l, kk.toList[l]! = kk[l]! := fun l => Array.getElem!_toList
  refine ⟨by rw [hs, h1]; simp, by rw [hs, h2]; simp [sprod, hl], fun i hi => ?_⟩
  rw [hs, h3 i (by simpa using hi)]
  simp [sprod, hl]

/-! ### `powsBelow` and `smallDivs` -/

/-- The list pushed by `powsBelow N1 q _ x f`: `x·q, x·q², …` while `< N1` (at most `f`). -/
def pbl (N1 q : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | x, f + 1 => if x * q < N1 then (x * q) :: pbl N1 q (x * q) f else []

theorem powsBelow_toList (N1 q : ℕ) :
    ∀ f (acc : Array ℕ) x, (powsBelow N1 q acc x f).toList = acc.toList ++ pbl N1 q x f := by
  intro f
  induction f with
  | zero => intro acc x; simp [powsBelow, pbl]
  | succ f ih =>
    intro acc x
    simp only [powsBelow, pbl]
    split_ifs
    · rw [ih, Array.toList_push]; simp
    · simp

theorem foldl_powsBelow_toList (N1 q e : ℕ) (L : List ℕ) :
    ∀ (init : Array ℕ), (L.foldl (fun acc d => powsBelow N1 q acc d e) init).toList =
      init.toList ++ L.flatMap (fun d => pbl N1 q d e) := by
  induction L with
  | nil => intro init; simp
  | cons d L ih =>
    intro init
    rw [List.foldl_cons, ih, powsBelow_toList, List.flatMap_cons, List.append_assoc]

theorem mem_pbl {N1 q : ℕ} (hq : 1 ≤ q) :
    ∀ f x y, y ∈ pbl N1 q x f ↔ ∃ t, 1 ≤ t ∧ t ≤ f ∧ y = x * q ^ t ∧ x * q ^ t < N1 := by
  intro f
  induction f with
  | zero => intro x y; simp only [pbl, List.not_mem_nil, false_iff]; rintro ⟨t, h1, h2, -⟩; omega
  | succ f ih =>
    intro x y
    simp only [pbl]
    split_ifs with h
    · rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨t, h1, h2, rfl, h4⟩)
        · exact ⟨1, le_rfl, by omega, by ring, by simpa using h⟩
        · exact ⟨t + 1, by omega, by omega, by ring, by rwa [pow_succ', ← mul_assoc]⟩
      · rintro ⟨t, h1, h2, rfl, h4⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | ht
        · left; ring
        · right
          refine ⟨t - 1, by omega, by omega, ?_, ?_⟩
          · rw [mul_assoc, ← pow_succ']; congr 2; omega
          · rw [mul_assoc, ← pow_succ']; rwa [show t - 1 + 1 = t by omega]
    · simp only [List.not_mem_nil, false_iff]
      rintro ⟨t, h1, h2, rfl, h4⟩
      apply h
      calc x * q = x * q ^ 1 := by ring
        _ ≤ x * q ^ t := Nat.mul_le_mul_left x (Nat.pow_le_pow_right hq h1)
        _ < N1 := h4

theorem pbl_pairwise {N1 q : ℕ} (hq : 2 ≤ q) :
    ∀ f x, 0 < x → (pbl N1 q x f).Pairwise (· < ·) := by
  intro f
  induction f with
  | zero => intro x _; simp [pbl]
  | succ f ih =>
    intro x hx
    simp only [pbl]
    split_ifs
    · rw [List.pairwise_cons]
      refine ⟨fun y hy => ?_, ih (x * q) (by positivity)⟩
      obtain ⟨t, h1, -, rfl, -⟩ := (mem_pbl (by omega) f (x * q) y).1 hy
      have : 1 < q ^ t := Nat.one_lt_pow (by omega) (by omega)
      have hxq : 0 < x * q := by positivity
      exact lt_mul_of_one_lt_right hxq this
    · exact List.Pairwise.nil

/-- The product `∏_{i < j} Sq[i]^{e i}` of the first `j` digits. -/
def npart (Sq : Array ℕ) (e : ℕ → ℕ) (j : ℕ) : ℕ := ∏ i ∈ range j, Sq[i]! ^ e i

/-- The Horner value `Σ_{i ∈ [j, n)} e i · ∏_{l ∈ [j, i)} (kk[l] + 1)` of the digits from `j` on. -/
def hornerFrom (kk : Array ℕ) (e : ℕ → ℕ) (n j : ℕ) : ℕ :=
  ∑ i ∈ Ico j n, e i * ∏ l ∈ Ico j i, (kk[l]! + 1)

theorem hornerFrom_succ (kk : Array ℕ) (e : ℕ → ℕ) {n j : ℕ} (hj : j < n) :
    hornerFrom kk e n j = e j + (kk[j]! + 1) * hornerFrom kk e n (j + 1) := by
  unfold hornerFrom
  rw [sum_eq_sum_Ico_succ_bot hj, Ico_self, prod_empty, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  rw [prod_eq_prod_Ico_succ_bot (by simp at hi; omega)]
  ring

theorem hornerFrom_zero (kk : Array ℕ) (e : ℕ → ℕ) (n : ℕ) :
    hornerFrom kk e n 0 = ∑ i ∈ range n, e i * sprod kk i := by
  unfold hornerFrom sprod
  rw [range_eq_Ico]
  refine sum_congr rfl fun i _ => ?_
  rw [range_eq_Ico]

theorem hornerFrom_self (kk : Array ℕ) (e : ℕ → ℕ) (n : ℕ) : hornerFrom kk e n n = 0 := by
  simp [hornerFrom]

section SmallDivs

variable {Sq kk : Array ℕ} {N1 : ℕ} {e : ℕ → ℕ}

theorem not_dvd_npart (hpr : ∀ i < Sq.size, (Sq[i]!).Prime)
    (hinj : ∀ i j, i < Sq.size → j < Sq.size → Sq[i]! = Sq[j]! → i = j) {j : ℕ}
    (hj : j < Sq.size) {d : ℕ} (hd : d ∣ npart Sq e j) : ¬ Sq[j]! ∣ d := by
  intro hqd
  have h := hqd.trans hd
  unfold npart at h
  obtain ⟨i, hi, hdiv⟩ := (Prime.dvd_finsetProd_iff (hpr j hj).prime _).1 h
  have hi' := mem_range.1 hi
  have := (Nat.prime_dvd_prime_iff_eq (hpr j hj) (hpr i (by omega))).1
    ((hpr j hj).dvd_of_dvd_pow hdiv)
  have := hinj j i hj (by omega) this
  omega

theorem npart_pos (hpr : ∀ i < Sq.size, (Sq[i]!).Prime) {j : ℕ} (hj : j ≤ Sq.size) :
    0 < npart Sq e j := by
  unfold npart
  exact prod_pos fun i hi => pow_pos (hpr i (by simp at hi; omega)).pos _

/-- One digit step of `smallDivs`: from the small divisors of `npart j` to those of
`npart (j + 1)`. -/
theorem smallDivs_step (hpr : ∀ i < Sq.size, (Sq[i]!).Prime)
    (hinj : ∀ i j, i < Sq.size → j < Sq.size → Sq[i]! = Sq[j]! → i = j) {j : ℕ}
    (hj : j < Sq.size) (ds : Array ℕ) (hnd : ds.toList.Nodup)
    (hmem : ∀ x, x ∈ ds.toList ↔ x ∣ npart Sq e j ∧ x < N1) :
    let ds' := ds.foldl (fun acc d => powsBelow N1 Sq[j]! acc d (e j)) ds
    ds'.toList.Nodup ∧ ∀ x, x ∈ ds'.toList ↔ x ∣ npart Sq e (j + 1) ∧ x < N1 := by
  intro ds'
  set q := Sq[j]! with hq_def
  have hqp : q.Prime := hpr j hj
  have hq2 : 2 ≤ q := hqp.two_le
  have hds' : ds'.toList = ds.toList ++ ds.toList.flatMap (fun d => pbl N1 q d (e j)) := by
    simp only [ds']
    rw [← Array.foldl_toList, foldl_powsBelow_toList]
  have hpos : ∀ d ∈ ds.toList, 0 < d := fun d hd =>
    Nat.pos_of_dvd_of_pos ((hmem d).1 hd).1 (npart_pos hpr hj.le)
  have hnq : ∀ d ∈ ds.toList, ¬ q ∣ d := fun d hd =>
    not_dvd_npart hpr hinj hj ((hmem d).1 hd).1
  have hnext : npart Sq e (j + 1) = npart Sq e j * q ^ e j := by
    unfold npart; rw [prod_range_succ]
  rw [hds']
  constructor
  · rw [List.nodup_append]
    refine ⟨hnd, ?_, ?_⟩
    · rw [List.nodup_flatMap]
      refine ⟨fun d hd => (pbl_pairwise hq2 (e j) d (hpos d hd)).nodup, ?_⟩
      refine hnd.imp_of_mem (fun {d d'} hd hd' hne => ?_)
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro x hx hx'
      obtain ⟨t, -, -, rfl, -⟩ := (mem_pbl (by omega) _ d x).1 hx
      obtain ⟨t', -, -, ht', -⟩ := (mem_pbl (by omega) _ d' _).1 hx'
      apply hne
      rcases lt_trichotomy t t' with h | rfl | h
      · exfalso
        have e1 : d * q ^ t = d' * q ^ (t' - t) * q ^ t := by
          rw [ht', mul_assoc, ← pow_add]; congr 2; omega
        have := Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) t) e1
        exact hnq d hd (this ▸ Dvd.dvd.mul_left (dvd_pow_self q (by omega)) d')
      · exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) t) ht'
      · exfalso
        have e1 : d' * q ^ t' = d * q ^ (t - t') * q ^ t' := by
          rw [← ht', mul_assoc, ← pow_add]; congr 2; omega
        have := Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) t') e1
        exact hnq d' hd' (this ▸ Dvd.dvd.mul_left (dvd_pow_self q (by omega)) d)
    · intro a ha b hb hab
      subst hab
      obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hb
      obtain ⟨t, ht1, -, rfl, -⟩ := (mem_pbl (by omega) _ d _).1 hx
      exact hnq _ ha (Dvd.dvd.mul_left (dvd_pow_self q (by omega)) d)
  · intro x
    rw [List.mem_append, hmem, List.mem_flatMap, hnext]
    constructor
    · rintro (⟨hx1, hx2⟩ | ⟨d, hd, hx⟩)
      · exact ⟨hx1.trans (dvd_mul_right _ _), hx2⟩
      · obtain ⟨t, -, ht2, rfl, ht4⟩ := (mem_pbl (by omega) _ d _).1 hx
        exact ⟨mul_dvd_mul ((hmem d).1 hd).1 (pow_dvd_pow q ht2), ht4⟩
    · rintro ⟨hx1, hx2⟩
      obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.1 hx1
      obtain ⟨t, ht, rfl⟩ := (Nat.dvd_prime_pow hqp).1 hz
      rcases Nat.eq_zero_or_pos t with rfl | ht0
      · left; exact ⟨by simpa using hy, by simpa using hx2⟩
      · right
        have hy0 : 0 < y := Nat.pos_of_dvd_of_pos hy (npart_pos hpr hj.le)
        have hyN : y < N1 := lt_of_le_of_lt (Nat.le_mul_of_pos_right y (pow_pos (by omega) t)) hx2
        exact ⟨y, (hmem y).2 ⟨hy, hyN⟩, (mem_pbl (by omega) _ y _).2 ⟨t, ht0, ht, rfl, hx2⟩⟩

/-- **`smallDivs`**: for digits `e i ≤ kk[i]` (`i < n = Sq.size`, distinct primes `Sq[i]`), the
array `smallDivs Sq kk N1 pat` at `pat = Σ_i e i · stride i` lists the divisors below `N1` of
`∏_i Sq[i]^{e i}`, without repetition. -/
theorem smallDivs_go_spec (hpr : ∀ i < Sq.size, (Sq[i]!).Prime)
    (hinj : ∀ i j, i < Sq.size → j < Sq.size → Sq[i]! = Sq[j]! → i = j)
    (he : ∀ i < Sq.size, e i ≤ kk[i]!) :
    ∀ f j r (ds : Array ℕ), j + f = Sq.size → r = hornerFrom kk e Sq.size j →
      ds.toList.Nodup → (∀ x, x ∈ ds.toList ↔ x ∣ npart Sq e j ∧ x < N1) →
      (smallDivs.go Sq kk N1 j r ds f).toList.Nodup ∧
        ∀ x, x ∈ (smallDivs.go Sq kk N1 j r ds f).toList ↔ x ∣ npart Sq e Sq.size ∧ x < N1 := by
  intro f
  induction f with
  | zero =>
    intro j r ds hj _ hnd hmem
    simp only [smallDivs.go]
    rw [show Sq.size = j by omega]
    exact ⟨hnd, hmem⟩
  | succ f ih =>
    intro j r ds hj hr hnd hmem
    have hjn : j < Sq.size := by omega
    simp only [smallDivs.go]
    have hrad : r % (kk[j]! + 1) = e j ∧ r / (kk[j]! + 1) = hornerFrom kk e Sq.size (j + 1) := by
      rw [hr, hornerFrom_succ kk e hjn]
      have h1 : e j < kk[j]! + 1 := Nat.lt_succ_of_le (he j hjn)
      constructor
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
      · rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h1, zero_add]
    rw [hrad.1, hrad.2]
    obtain ⟨h1, h2⟩ := smallDivs_step (N1 := N1) (e := e) hpr hinj hjn ds hnd hmem
    exact ih (j + 1) _ _ (by omega) rfl h1 h2

theorem smallDivs_spec (hpr : ∀ i < Sq.size, (Sq[i]!).Prime)
    (hinj : ∀ i j, i < Sq.size → j < Sq.size → Sq[i]! = Sq[j]! → i = j)
    (he : ∀ i < Sq.size, e i ≤ kk[i]!) (hN1 : 1 < N1) :
    (smallDivs Sq kk N1 (∑ i ∈ range Sq.size, e i * sprod kk i)).toList.Nodup ∧
      ∀ x, x ∈ (smallDivs Sq kk N1 (∑ i ∈ range Sq.size, e i * sprod kk i)).toList ↔
        x ∣ npart Sq e Sq.size ∧ x < N1 := by
  unfold smallDivs
  refine smallDivs_go_spec hpr hinj he Sq.size 0 _ #[1] (by omega)
    (hornerFrom_zero kk e Sq.size).symm (by simp) fun x => ?_
  simp only [List.mem_singleton, npart, range_zero, prod_empty, Nat.dvd_one]
  constructor
  · rintro rfl; exact ⟨rfl, hN1⟩
  · rintro ⟨rfl, -⟩; rfl

end SmallDivs


/-! ### `sumCd`, `profileOf` -/

theorem foldl_add_eq (f : ℕ → ℕ) (L : List ℕ) :
    ∀ a, L.foldl (fun acc d => acc + f d) a = a + (L.map f).sum := by
  induction L with
  | nil => intro a; simp
  | cons x L ih => intro a; rw [List.foldl_cons, ih]; simp; ring

theorem foldl_count_eq (p : ℕ → Prop) [DecidablePred p] (L : List ℕ) :
    ∀ a, L.foldl (fun c d => if p d then c + 1 else c) a = a + (L.filter (fun d => decide (p d))).length := by
  induction L with
  | nil => intro a; simp
  | cons x L ih =>
    intro a
    rw [List.foldl_cons, ih, List.filter_cons]
    by_cases hx : p x
    · simp [hx]; ring
    · simp [hx]

theorem sumCd_eq (cd ds : Array ℕ) : sumCd cd ds = (ds.toList.map (fun d => cd[d]!)).sum := by
  unfold sumCd
  rw [← Array.foldl_toList, foldl_add_eq, zero_add]

theorem profileOf_size (Bq ds : Array ℕ) (N1 : ℕ) : (profileOf Bq ds N1).size = Bq.size := by
  simp [profileOf]

theorem profileOf_get (Bq ds : Array ℕ) (N1 : ℕ) {i : ℕ} (hi : i < Bq.size) :
    (profileOf Bq ds N1)[i]! = (ds.toList.filter (fun d => decide (d * Bq[i]! < N1))).length := by
  unfold profileOf
  rw [getElem!_map _ _ hi]
  rw [← Array.foldl_toList, foldl_count_eq (fun d => d * Bq[i]! < N1), zero_add]

/-! ### `patternData` -/

theorem patternData_go_spec (Sq kk Bq cd : Array ℕ) (N1 : ℕ) :
    ∀ f pat (patF patProf : Array ℕ) (profs : Array (Array ℕ)),
      patF.size = pat → patProf.size = pat →
      (∀ i, i < pat → patF[i]! = sumCd cd (smallDivs Sq kk N1 i) ∧ patProf[i]! < profs.size ∧
        profs[patProf[i]!]! = profileOf Bq (smallDivs Sq kk N1 i) N1) →
      ∀ i, i < pat + f →
        (patternData.go Sq kk Bq cd N1 pat f patF patProf profs).1[i]! =
            sumCd cd (smallDivs Sq kk N1 i) ∧
          (patternData.go Sq kk Bq cd N1 pat f patF patProf profs).2.1[i]! <
            (patternData.go Sq kk Bq cd N1 pat f patF patProf profs).2.2.size ∧
          (patternData.go Sq kk Bq cd N1 pat f patF patProf profs).2.2[
              (patternData.go Sq kk Bq cd N1 pat f patF patProf profs).2.1[i]!]! =
            profileOf Bq (smallDivs Sq kk N1 i) N1 := by
  intro f
  induction f with
  | zero =>
    intro pat patF patProf profs _ _ hinv i hi
    simp only [patternData.go]
    exact hinv i (by omega)
  | succ f ih =>
    intro pat patF patProf profs hF hP hinv i hi
    simp only [patternData.go]
    split
    · rename_i k hk
      obtain ⟨hk1, hk2, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hk
      have hk2' : profs[k]! = profileOf Bq (smallDivs Sq kk N1 pat) N1 := by
        rw [getElem!_of_lt _ hk1]; exact (beq_iff_eq.1 hk2)
      refine ih (pat + 1) _ _ profs (by simp [hF]) (by simp [hP]) (fun i' hi' => ?_) i (by omega)
      by_cases hi'p : i' < pat
      · rw [getElem!_push_lt _ _ (by omega), getElem!_push_lt _ _ (by omega)]
        exact hinv i' hi'p
      · have : i' = pat := by omega
        rw [this, getElem!_push_of_eq _ _ hF, getElem!_push_of_eq _ _ hP]
        exact ⟨rfl, hk1, hk2'⟩
    · rename_i hk
      refine ih (pat + 1) _ _ _ (by simp [hF]) (by simp [hP]) (fun i' hi' => ?_) i (by omega)
      by_cases hi'p : i' < pat
      · rw [getElem!_push_lt _ _ (by omega), getElem!_push_lt _ _ (by omega)]
        obtain ⟨h1, h2, h3⟩ := hinv i' hi'p
        refine ⟨h1, by simp; omega, ?_⟩
        rw [getElem!_push_lt _ _ h2, h3]
      · have : i' = pat := by omega
        rw [this, getElem!_push_of_eq _ _ hF, getElem!_push_of_eq _ _ hP, getElem!_push_size]
        exact ⟨rfl, by simp, rfl⟩

theorem patternData_spec (Sq kk Bq cd : Array ℕ) (N1 npat : ℕ) {pat : ℕ} (hpat : pat < npat) :
    (patternData Sq kk Bq cd N1 npat).1[pat]! = sumCd cd (smallDivs Sq kk N1 pat) ∧
      (patternData Sq kk Bq cd N1 npat).2.1[pat]! < (patternData Sq kk Bq cd N1 npat).2.2.size ∧
      (patternData Sq kk Bq cd N1 npat).2.2[(patternData Sq kk Bq cd N1 npat).2.1[pat]!]! =
        profileOf Bq (smallDivs Sq kk N1 pat) N1 := by
  unfold patternData
  exact patternData_go_spec Sq kk Bq cd N1 npat 0 _ _ #[] (by simp) (by simp)
    (fun i hi => absurd hi (Nat.not_lt_zero i)) pat (by omega)

/-! ### `corrSum` -/

/-- The contribution of the row `b` to `corrSum` (see `SBH.corrSum`). -/
def corrTerm (tab : ProfTab) (β0 om τ b : ℕ) : ℕ :=
  if cdiv (β0 + b * om) τ < W48 then 0
  else mulUp (cdiv (β0 + b * om) τ) (tab.S0[b]!)[cdiv (β0 + b * om) τ >>> 48]! -
    (tab.S1W[b]!)[cdiv (β0 + b * om) τ >>> 48]!

theorem corrSum_spec (tab : ProfTab) (β0 om τ : ℕ) :
    ∀ f b acc ok, (corrSum tab β0 om τ b f acc ok).2 = true →
      ok = true ∧
      (∀ b', b ≤ b' → b' < b + f → W48 ≤ cdiv (β0 + b' * om) τ →
        cdiv (β0 + b' * om) τ >>> 48 ≤ tab.K) ∧
      (corrSum tab β0 om τ b f acc ok).1 = acc + ∑ b' ∈ Ico b (b + f), corrTerm tab β0 om τ b' := by
  intro f
  induction f with
  | zero =>
    intro b acc ok h
    simp only [corrSum] at h ⊢
    exact ⟨h, fun b' h1 h2 => by omega, by simp⟩
  | succ f ih =>
    intro b acc ok h
    simp only [corrSum] at h ⊢
    have hsplit : ∑ b' ∈ Ico b (b + (f + 1)), corrTerm tab β0 om τ b' =
        corrTerm tab β0 om τ b + ∑ b' ∈ Ico (b + 1) (b + 1 + f), corrTerm tab β0 om τ b' := by
      rw [sum_eq_sum_Ico_succ_bot (by omega), show b + (f + 1) = b + 1 + f by omega]
    split_ifs at h ⊢ with h1 h2
    · obtain ⟨hok, hK, hval⟩ := ih (b + 1) acc ok h
      refine ⟨hok, fun b' hb1 hb2 hb3 => ?_, ?_⟩
      · rcases Nat.eq_or_lt_of_le hb1 with rfl | hb
        · exact absurd hb3 (not_le.2 h1)
        · exact hK b' hb (by omega) hb3
      · rw [hval, hsplit, corrTerm, ite_eq_left h1, zero_add]
    · obtain ⟨hok, -, -⟩ := ih (b + 1) acc false h
      exact absurd hok (by simp)
    · obtain ⟨hok, hK, hval⟩ := ih (b + 1) _ ok h
      refine ⟨hok, fun b' hb1 hb2 hb3 => ?_, ?_⟩
      · rcases Nat.eq_or_lt_of_le hb1 with rfl | hb
        · exact not_lt.1 h2
        · exact hK b' hb (by omega) hb3
      · rw [hval, hsplit, corrTerm, ite_eq_right h1]
        omega

/-! ### The DFS: `ok` monotonicity -/

section DFS

variable (c : DfsCfg)

theorem leafAdd_eq (P τ pat : ℕ) (acc : DfsAcc) :
    leafAdd c P τ pat acc =
      { acc with
        leaf := acc.leaf + mulUp P
          (leafValue c.tabs[c.patProf[pat]!]! c.patF[pat]! τ c.ETW c.tp1 c.om c.omP).1
        nleaf := acc.nleaf + 1
        ok := acc.ok &&
          (leafValue c.tabs[c.patProf[pat]!]! c.patF[pat]! τ c.ETW c.tp1 c.om c.omP).2 } := rfl

theorem dfs_ok_mono :
    ∀ f, (∀ j P τ pat acc, (dfsNode c f j P τ pat acc).ok = true → acc.ok = true) ∧
      (∀ j a P τ pat acc, (dfsExp c f j a P τ pat acc).ok = true → acc.ok = true) := by
  intro f
  induction f with
  | zero =>
    refine ⟨fun j P τ pat acc h => ?_, fun j a P τ pat acc h => ?_⟩
    · rw [dfsNode] at h; simp at h
    · rw [dfsExp] at h; simp at h
  | succ f ih =>
    refine ⟨fun j P τ pat acc h => ?_, fun j a P τ pat acc h => ?_⟩
    · rw [dfsNode] at h
      split_ifs at h
      · exact ih.2 _ _ _ _ _ _ h
      · rw [leafAdd_eq] at h
        simp only [Bool.and_eq_true] at h
        exact h.1
    · rw [dfsExp] at h
      split_ifs at h
      · exact h
      · exact ih.1 _ _ _ _ _ (ih.2 _ _ _ _ _ _ h)

end DFS


/-! ### Real values of P- and W-values -/

theorem pv_nonneg' (x : ℕ) : 0 ≤ pv x := by unfold pv; positivity

theorem wv_nonneg (x : ℕ) : 0 ≤ wv x := by unfold wv; positivity

theorem wv_add (x y : ℕ) : wv (x + y) = wv x + wv y := by unfold wv; push_cast; ring

theorem pv_add' (x y : ℕ) : pv (x + y) = pv x + pv y := by unfold pv; push_cast; ring

theorem wv_mono {x y : ℕ} (h : x ≤ y) : wv x ≤ wv y := by
  unfold wv; gcongr

theorem pv_mono' {x y : ℕ} (h : x ≤ y) : pv x ≤ pv y := by
  unfold pv; gcongr

theorem wv_sub_ge (x y : ℕ) : wv x - wv y ≤ wv (x - y) := by
  unfold wv
  rw [← sub_div]
  gcongr
  have : ((x - y : ℕ) : ℝ) ≥ (x : ℝ) - y := by
    rcases le_total y x with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h
  linarith

theorem ONE_real' : (ONE : ℝ) = 2 ^ 62 := by rw [ONE_eq]; norm_num

theorem pv_mul_le_mulUp' (x y : ℕ) : pv x * pv y ≤ pv (mulUp x y) := by
  have h1 := mulUp_spec x y
  have h2 : (x : ℝ) * y ≤ (mulUp x y : ℝ) * ONE := by exact_mod_cast h1
  rw [ONE_real'] at h2
  unfold pv
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem pv_mul_wv_le_mulUp (x y : ℕ) : pv x * wv y ≤ wv (mulUp x y) := by
  have h1 := mulUp_spec x y
  have h2 : (x : ℝ) * y ≤ (mulUp x y : ℝ) * ONE := by exact_mod_cast h1
  rw [ONE_real'] at h2
  unfold pv wv
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem wv_mul_pv_le_mulUp (x y : ℕ) : wv x * pv y ≤ wv (mulUp x y) := by
  have h1 := mulUp_spec x y
  have h2 : (x : ℝ) * y ≤ (mulUp x y : ℝ) * ONE := by exact_mod_cast h1
  rw [ONE_real'] at h2
  unfold pv wv
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem wv_natMul (a x : ℕ) : wv (a * x) = (a : ℝ) * wv x := by
  unfold wv; push_cast; ring

/-! ### The DFS: soundness by induction on the fuel -/

section DFSSound

variable (c : DfsCfg) (Q : ℕ → ℕ) (N : ℕ) (ρ : ℕ → ℕ → ℝ) (V : ℕ → (ℕ → ℕ) → ℝ)
  (I : ℕ → (ℕ → ℕ) → ℕ → ℕ → Prop)

/-- The accumulated W-value `leaf + prune` of the DFS. -/
noncomputable def accW (acc : DfsAcc) : ℝ := wv (acc.leaf + acc.prune)

/-- **Abstract soundness of `dfsNode`/`dfsExp`.** `I j u τ pat` is the node invariant (`u` the
exponents chosen so far, `τ`, `pat` the code's running values), `V j u` the quantity to bound at
a node, `ρ j a` the law of the exponent of the `j`-th prime (caps `N`). Hypotheses: the
invariant is preserved by the code's step, leaves add at least `P·V`, `V` splits over the next
exponent, a pruned subtree `{v_j ≥ a}` is bounded by the code's `bnd`, the code's point masses
are upper bounds. Conclusion: the DFS adds at least `pv P · V j u`. -/
theorem dfs_sound
    (hstep : ∀ j u τ pat a, j < c.nS → I j u τ pat → a ≤ c.acut[j]! →
      I (j + 1) (Function.update u (Q j) a) (τ * (a + 1)) (pat + min a c.kk[j]! * c.stride[j]!))
    (hleaf : ∀ j u τ pat P acc, ¬ j < c.nS → I j u τ pat → (leafAdd c P τ pat acc).ok = true →
      accW acc + pv P * V j u ≤ accW (leafAdd c P τ pat acc))
    (hsplit : ∀ j u τ pat, j < c.nS → I j u τ pat →
      V j u = ∑ a ∈ range (N + 1), ρ j a * V (j + 1) (Function.update u (Q j) a))
    (hprune : ∀ j u τ pat a P, j < c.nS → I j u τ pat → a ≤ c.acut[j]! + 1 →
      pv P * ∑ a' ∈ Ico a (N + 1), ρ j a' * V (j + 1) (Function.update u (Q j) a') ≤
        wv (τ * mulUp (mulUp P (c.h[j]!)[a]!) c.REW[j + 1]!))
    (hρ : ∀ j a, j < c.nS → a ≤ c.acut[j]! → ρ j a ≤ pv (c.pm[j]!)[a]!)
    (hacut : ∀ j, j < c.nS → c.acut[j]! < N)
    (hV0 : ∀ j u τ pat, I j u τ pat → 0 ≤ V j u) :
    ∀ f, (∀ j u τ pat P acc, I j u τ pat → (dfsNode c f j P τ pat acc).ok = true →
        accW acc + pv P * V j u ≤ accW (dfsNode c f j P τ pat acc)) ∧
      (∀ j a u τ pat P acc, j < c.nS → I j u τ pat → a ≤ c.acut[j]! + 1 →
        (dfsExp c f j a P τ pat acc).ok = true →
        accW acc + pv P * ∑ a' ∈ Ico a (N + 1), ρ j a' * V (j + 1) (Function.update u (Q j) a') ≤
          accW (dfsExp c f j a P τ pat acc)) := by
  intro f
  induction f with
  | zero =>
    refine ⟨fun j u τ pat P acc _ h => ?_, fun j a u τ pat P acc _ _ _ h => ?_⟩
    · rw [dfsNode] at h; simp at h
    · rw [dfsExp] at h; simp at h
  | succ f ih =>
    refine ⟨fun j u τ pat P acc hI h => ?_, fun j a u τ pat P acc hj hI ha h => ?_⟩
    · rw [dfsNode] at h ⊢
      split_ifs at h ⊢ with hj
      · have := ih.2 j 0 u τ pat P acc hj hI (Nat.zero_le _) h
        rw [hsplit j u τ pat hj hI, range_eq_Ico]
        exact this
      · exact hleaf j u τ pat P acc hj hI h
    · rw [dfsExp] at h ⊢
      split_ifs at h ⊢ with hpr
      · -- pruned
        have hb := hprune j u τ pat a P hj hI ha
        unfold accW
        simp only
        rw [← Nat.add_assoc, wv_add (acc.leaf + acc.prune)]
        linarith
      · -- recurse into `v_j = a`, then continue with `a + 1`
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hpr
        obtain ⟨hacj, -⟩ := hpr
        set acc1 := dfsNode c f (j + 1) (mulUp P (c.pm[j]!)[a]!) (τ * (a + 1))
          (pat + min a c.kk[j]! * c.stride[j]!) acc with hacc1
        have hok1 : acc1.ok = true := (dfs_ok_mono c f).2 _ _ _ _ _ _ h
        have h1 := ih.1 (j + 1) (Function.update u (Q j) a) (τ * (a + 1))
          (pat + min a c.kk[j]! * c.stride[j]!) (mulUp P (c.pm[j]!)[a]!) acc
          (hstep j u τ pat a hj hI hacj) hok1
        have h2 := ih.2 j (a + 1) u τ pat P acc1 hj hI (by omega) h
        have hsum : ∑ a' ∈ Ico a (N + 1), ρ j a' * V (j + 1) (Function.update u (Q j) a') =
            ρ j a * V (j + 1) (Function.update u (Q j) a) +
              ∑ a' ∈ Ico (a + 1) (N + 1), ρ j a' * V (j + 1) (Function.update u (Q j) a') :=
          sum_eq_sum_Ico_succ_bot (by have := hacut j hj; omega) _
        have hV := hV0 _ _ _ _ (hstep j u τ pat a hj hI hacj)
        have hP : pv P * ρ j a ≤ pv (mulUp P (c.pm[j]!)[a]!) :=
          (mul_le_mul_of_nonneg_left (hρ j a hj hacj) (pv_nonneg' P)).trans
            (pv_mul_le_mulUp' _ _)
        have h3 : pv P * (ρ j a * V (j + 1) (Function.update u (Q j) a)) ≤
            pv (mulUp P (c.pm[j]!)[a]!) * V (j + 1) (Function.update u (Q j) a) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hP hV
        rw [hsum, mul_add]
        linarith

end DFSSound

end MinModulus.Checker2Sound.D
