import MinModulus.CheckerImpl.Checker
import MinModulus.CheckerMath.ComparisonBound

/-!
# `CheckerSound.EnumBasic` (agent CS-C): building blocks for the enumeration semantics

Status: complete, no `sorry`.

Pure lemmas about the pieces of `CheckerImpl.Enum` (no recursion over the primes yet; that is
`EnumSem.lean`):
* arrays read with default `0` (`getD0`): `getD0_set!`, `getD0_growAdd` (`growAdd` adds `v` at
  index `i`), `getD0_of_size_le`, `getD0_eq_getElem!`;
* `seg buf lo hi`: the multiset of the entries `buf[lo..hi)` (`card_seg`, `seg_cons`,
  `seg_split`, `seg_congr`, `seg_eq_zero`);
* `view acc : Fin 5 → ℕ → ℕ`: the five accumulator arrays `pen, hn, hs1, hs2, fb`, and
  `leafView`, what one call of `leaf` adds to them (`view_leaf`, `leaf_buf`, `leaf_ok`);
* `extendBlock_spec`: `extendBlock` appends `(buf[i..be) · q) ∩ [0, M1)` at `len, len+1, …`,
  counts the appended entries `< M2`, does not touch `buf[0..len)` nor the five arrays;
* divisors: `divisors_mul_pow_val` (the divisors of `s q^a` are those of `s q^(a-1)` plus the
  `e q^a`, `e ∣ s`, for `q` prime coprime to `s`), `filter_map_mul_filter` (the block recursion
  of `extendBlock`), `countP_filter_of_le`;
* `sum_box_insert`: the decomposition `box (insert q S) ≅ [0, γ q] × box S` for sums with values
  in any additive commutative monoid (the unweighted analogue of `Smooth.expect_insert`).
-/

namespace MinModulus.CheckerSound.C

open MinModulus.CheckerImpl MinModulus.Smooth Finset

/-! ### Arrays of naturals read with default `0` -/

theorem getD0_eq (a : Array ℕ) (i : ℕ) : getD0 a i = a[i]?.getD 0 := by
  unfold getD0
  rw [Array.getD_eq_getD_getElem?]

theorem getD0_eq_getElem! (a : Array ℕ) (i : ℕ) : getD0 a i = a[i]! := by
  rw [getD0_eq, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rfl

theorem getD0_of_size_le {a : Array ℕ} {i : ℕ} (h : a.size ≤ i) : getD0 a i = 0 := by
  rw [getD0_eq, Array.getElem?_eq_none h]
  rfl

@[simp] theorem getD0_empty (i : ℕ) : getD0 #[] i = 0 := getD0_of_size_le (by simp)

theorem size_set! (a : Array ℕ) (i v : ℕ) : (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem getD0_set! (a : Array ℕ) (i v j : ℕ) :
    getD0 (a.set! i v) j = if j = i ∧ i < a.size then v else getD0 a j := by
  rw [getD0_eq, getD0_eq, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < a.size
    · simp [h2]
    · simp [h2]
  · have : ¬ (j = i ∧ i < a.size) := fun h => h1 h.1.symm
    simp [h1, this]

/-- `growAdd a i v` adds `v` at index `i` (growing the array if needed). -/
theorem getD0_growAdd (a : Array ℕ) (i v j : ℕ) :
    getD0 (growAdd a i v) j = getD0 a j + if j = i then v else 0 := by
  unfold growAdd
  split_ifs with h hj hj
  · subst hj
    rw [getD0_set!, ite_eq_left ⟨rfl, h⟩, getD0_eq_getElem!]
  · rw [getD0_set!, ite_eq_right (fun h' => hj h'.1), Nat.add_zero]
  · subst hj
    rw [getD0_set!, ite_eq_left ⟨rfl, by simp [Array.size_append]; omega⟩,
      getD0_of_size_le (by omega), Nat.zero_add]
  · rw [getD0_set!, ite_eq_right (fun h' => hj h'.1), Nat.add_zero, getD0_eq, getD0_eq,
      Array.getElem?_append]
    split_ifs with h2
    · rfl
    · rw [Array.getElem?_replicate, Array.getElem?_eq_none (Nat.le_of_not_lt h2)]
      split_ifs <;> rfl

/-! ### Segments of the divisor buffer -/

/-- The multiset of the entries `buf[lo], …, buf[hi-1]` (read with default `0`). -/
def seg (buf : Array ℕ) (lo hi : ℕ) : Multiset ℕ :=
  (((List.range' lo (hi - lo)).map (getD0 buf) : List ℕ) : Multiset ℕ)

theorem card_seg (buf : Array ℕ) (lo hi : ℕ) : Multiset.card (seg buf lo hi) = hi - lo := by
  simp [seg]

theorem seg_eq_zero {buf : Array ℕ} {lo hi : ℕ} (h : hi ≤ lo) : seg buf lo hi = 0 := by
  simp [seg, Nat.sub_eq_zero_of_le h]

theorem seg_cons (buf : Array ℕ) {lo hi : ℕ} (h : lo < hi) :
    seg buf lo hi = getD0 buf lo ::ₘ seg buf (lo + 1) hi := by
  unfold seg
  obtain ⟨k, hk⟩ : ∃ k, hi - lo = k + 1 := ⟨hi - lo - 1, by omega⟩
  have hk' : hi - (lo + 1) = k := by omega
  rw [hk, hk', List.range'_succ, List.map_cons, Multiset.cons_coe]

theorem seg_split (buf : Array ℕ) {lo mid hi : ℕ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    seg buf lo hi = seg buf lo mid + seg buf mid hi := by
  unfold seg
  rw [Multiset.coe_add, ← List.map_append]
  congr 2
  have := @List.range'_append lo (mid - lo) (hi - mid) 1
  simp only [Nat.one_mul] at this
  rw [Nat.add_sub_cancel' h1] at this
  rw [this]
  congr 1
  omega

theorem seg_congr {b1 b2 : Array ℕ} {lo hi : ℕ}
    (h : ∀ j, lo ≤ j → j < hi → getD0 b1 j = getD0 b2 j) : seg b1 lo hi = seg b2 lo hi := by
  unfold seg
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range'] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact h _ (by omega) (by omega)

theorem seg_single (buf : Array ℕ) (lo : ℕ) : seg buf lo (lo + 1) = {getD0 buf lo} := by
  rw [seg_cons buf (Nat.lt_succ_self lo), seg_eq_zero le_rfl]
  rfl

/-! ### The accumulator arrays and one leaf -/

/-- The five accumulator arrays of the enumeration, read with default `0`:
`0 ↦ pen`, `1 ↦ hn`, `2 ↦ hs1`, `3 ↦ hs2`, `4 ↦ fb`. -/
def view (acc : EnumAcc) : Fin 5 → ℕ → ℕ
  | 0, j => getD0 acc.pen j
  | 1, j => getD0 acc.hn j
  | 2, j => getD0 acc.hs1 j
  | 3, j => getD0 acc.hs2 j
  | 4, j => getD0 acc.fb j

/-- What one leaf (`s`, `τ`, `pat`, `σ1`, `σ2`) adds to the five arrays (see `leaf`), with
`n1 = τ - σ1`, `I = pj1·n1 + pj2·(σ1 - σ2) + σ2`, `pu = ⌈cup[pat]/s⌉`, `pl = ⌊clo[pat]/s⌋`. -/
def leafView (cfg : EnumCfg) (s τ pat σ1 σ2 : ℕ) : Fin 5 → ℕ → ℕ
  | 0, j => if τ ≤ cfg.kmax ∧ j = τ then getD0 cfg.clo pat / s else 0
  | 1, j => if cfg.It ≤ cfg.pj1 * (τ - σ1) + cfg.pj2 * (σ1 - σ2) + σ2 ∧ j = τ - σ1
      then cdiv (getD0 cfg.cup pat) s else 0
  | 2, j => if cfg.It ≤ cfg.pj1 * (τ - σ1) + cfg.pj2 * (σ1 - σ2) + σ2 ∧ j = σ1
      then cdiv (getD0 cfg.cup pat) s else 0
  | 3, j => if cfg.It ≤ cfg.pj1 * (τ - σ1) + cfg.pj2 * (σ1 - σ2) + σ2 ∧ j = σ2
      then cdiv (getD0 cfg.cup pat) s else 0
  | 4, j => if ¬ cfg.It ≤ cfg.pj1 * (τ - σ1) + cfg.pj2 * (σ1 - σ2) + σ2 ∧
      j = ((τ - σ1) * cfg.M1 + σ1) * cfg.M2 + σ2 then cdiv (getD0 cfg.cup pat) s else 0

theorem view_leaf (cfg : EnumCfg) (s τ pat σ1 σ2 : ℕ) (acc : EnumAcc) :
    view (leaf cfg s τ pat σ1 σ2 acc) = view acc + leafView cfg s τ pat σ1 σ2 := by
  funext k j
  obtain ⟨buf, pen, hn, hs1, hs2, fb, nleaf, ok⟩ := acc
  simp only [leaf, Pi.add_apply]
  split_ifs with hI <;> fin_cases k <;>
    simp [view, leafView, getD0_growAdd, hI] <;> (try split_ifs) <;> simp_all

theorem leaf_buf (cfg : EnumCfg) (s τ pat σ1 σ2 : ℕ) (acc : EnumAcc) :
    (leaf cfg s τ pat σ1 σ2 acc).buf = acc.buf := by
  obtain ⟨buf, pen, hn, hs1, hs2, fb, nleaf, ok⟩ := acc
  simp only [leaf]
  split_ifs <;> rfl

theorem leaf_ok (cfg : EnumCfg) (s τ pat σ1 σ2 : ℕ) (acc : EnumAcc)
    (h : (leaf cfg s τ pat σ1 σ2 acc).ok = true) : acc.ok = true := by
  obtain ⟨buf, pen, hn, hs1, hs2, fb, nleaf, ok⟩ := acc
  simp only [leaf] at h
  split_ifs at h <;> simp_all

/-! ### `extendBlock` -/

/-- **`extendBlock`**: reads `buf[i..be)` (below `len`), appends `e·q` for every read `e` with
`e·q < M1` at `len, len+1, …`, and counts the appended entries `< M2`; `buf[0..len)`, the size
of `buf` and the five arrays are unchanged. (Only when the final `ok` is `true`.) -/
theorem extendBlock_spec (cfg : EnumCfg) (q be : ℕ) :
    ∀ (fuel i len sig2 : ℕ) (acc : EnumAcc) (acc' : EnumAcc) (len' sig2' : ℕ),
    extendBlock cfg q be i len sig2 acc fuel = (acc', len', sig2') → be ≤ len →
    acc'.ok = true →
    acc.ok = true ∧ view acc' = view acc ∧ acc'.buf.size = acc.buf.size ∧
    (∀ j < len, getD0 acc'.buf j = getD0 acc.buf j) ∧ len ≤ len' ∧
    seg acc'.buf len len' = ((seg acc.buf i be).map (· * q)).filter (· < cfg.M1) ∧
    sig2' = sig2 + (((seg acc.buf i be).map (· * q)).filter (· < cfg.M1)).countP (· < cfg.M2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i len sig2 acc acc' len' sig2' h hle hok
    rw [extendBlock] at h
    split_ifs at h with hib
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      simp at hok
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [seg_eq_zero (Nat.le_of_not_lt hib), seg_eq_zero le_rfl]
      simp_all
  | succ f ih =>
    intro i len sig2 acc acc' len' sig2' h hle hok
    rw [extendBlock] at h
    simp only at h
    generalize hS : (if getD0 acc.buf i * q < cfg.M2 then sig2 + 1 else sig2) = S at h
    split_ifs at h with hib hv hlen
    · -- append `v = buf[i]·q` at position `len`
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih _ _ _ _ _ _ _ h (by omega) hok
      simp only at h1 h2 h3 h4 h5 h6 h7
      have hseg : seg (acc.buf.set! len (getD0 acc.buf i * q)) (i + 1) be =
          seg acc.buf (i + 1) be :=
        seg_congr fun j _ hj => by rw [getD0_set!, ite_eq_right (by omega)]
      refine ⟨h1, h2.trans (by funext k j; fin_cases k <;> rfl), h3.trans (size_set! _ _ _),
        fun j hj => (h4 j (by omega)).trans ?_, by omega, ?_, ?_⟩
      · rw [getD0_set!, ite_eq_right (by omega)]
      · rw [seg_cons _ (show len < len' by omega), h4 len (Nat.lt_succ_self _), getD0_set!,
          ite_eq_left ⟨rfl, hlen⟩, h6, hseg, seg_cons _ hib, Multiset.map_cons,
          Multiset.filter_cons_of_pos (p := fun x => x < cfg.M1) _ hv]
      · rw [h7, hseg, seg_cons _ hib, Multiset.map_cons,
          Multiset.filter_cons_of_pos (p := fun x => x < cfg.M1) _ hv, Multiset.countP_cons, ← hS]
        split_ifs <;> omega
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      simp at hok
    · subst hS
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih _ _ _ _ _ _ _ h hle hok
      refine ⟨h1, h2, h3, h4, h5, ?_, ?_⟩
      · rw [h6, seg_cons _ hib, Multiset.map_cons,
          Multiset.filter_cons_of_neg (p := fun x => x < cfg.M1) _ hv]
      · rw [h7, seg_cons _ hib, Multiset.map_cons,
          Multiset.filter_cons_of_neg (p := fun x => x < cfg.M1) _ hv]
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [seg_eq_zero (Nat.le_of_not_lt hib), seg_eq_zero le_rfl]
      simp_all

/-! ### Divisors -/

/-- Divisors of `s q^a` (`q` prime, coprime to `s`, `a ≥ 1`): those of `s q^(a-1)` and the
`e q^a` with `e ∣ s`. -/
theorem divisors_mul_pow_val {s q a : ℕ} (hs : 0 < s) (hq : q.Prime) (hqs : Nat.Coprime q s)
    (ha : 1 ≤ a) :
    (s * q ^ a).divisors.val =
      (s * q ^ (a - 1)).divisors.val + s.divisors.val.map (· * q ^ a) := by
  have hqa : 0 < q ^ a := pow_pos hq.pos a
  have hinj : Function.Injective (· * q ^ a) := fun x y h => Nat.eq_of_mul_eq_mul_right hqa h
  have hsa : s * q ^ a ≠ 0 := Nat.mul_ne_zero hs.ne' hqa.ne'
  have hsa1 : s * q ^ (a - 1) ≠ 0 := Nat.mul_ne_zero hs.ne' (pow_pos hq.pos _).ne'
  rw [Multiset.Nodup.ext (s * q ^ a).divisors.nodup ?_]
  · intro d
    rw [Multiset.mem_add, Multiset.mem_map]
    simp only [Finset.mem_val, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      obtain ⟨d1, d2, hd1, hd2, rfl⟩ := Nat.dvd_mul.1 hd
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hq).1 hd2
      rcases Nat.lt_or_ge j a with hja | hja
      · left
        exact ⟨Nat.mul_dvd_mul hd1 (Nat.pow_dvd_pow q (by omega)), hsa1⟩
      · right
        refine ⟨d1, ⟨hd1, hs.ne'⟩, ?_⟩
        rw [le_antisymm hj hja]
    · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
      · exact ⟨hd.trans (Nat.mul_dvd_mul_left s (Nat.pow_dvd_pow q (by omega))), hsa⟩
      · exact ⟨Nat.mul_dvd_mul_right he _, hsa⟩
  · rw [Multiset.nodup_add]
    refine ⟨(s * q ^ (a - 1)).divisors.nodup, Multiset.Nodup.map hinj s.divisors.nodup, ?_⟩
    rw [Multiset.disjoint_left]
    intro d hd hd'
    rw [Finset.mem_val, Nat.mem_divisors] at hd
    obtain ⟨e, -, rfl⟩ := Multiset.mem_map.1 hd'
    have h1 : q ^ a ∣ s * q ^ (a - 1) := (Dvd.intro_left e rfl).trans hd.1
    have hcop : Nat.Coprime (q ^ a) s := Nat.Coprime.pow_left a hqs
    have h2 : q ^ a ∣ q ^ (a - 1) := by
      rw [mul_comm] at h1
      exact hcop.dvd_of_dvd_mul_right h1
    have := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).1 h2
    omega

/-- The block recursion of `extendBlock`: filtering by `· < M`, multiplying by `q ≥ 1` and
filtering again is multiplying by `q` and filtering once. -/
theorem filter_map_mul_filter (S : Multiset ℕ) {q M c : ℕ} (hq : 1 ≤ q) :
    ((((S.map (· * c)).filter (· < M)).map (· * q)).filter (· < M)) =
      (S.map (· * (c * q))).filter (· < M) := by
  rw [Multiset.filter_map, Multiset.filter_filter, Multiset.filter_map, Multiset.map_map,
    Multiset.filter_map]
  congr 1
  · funext x
    simp [Function.comp, mul_assoc]
  · refine Multiset.filter_congr fun x _ => ?_
    simp only [Function.comp]
    rw [← mul_assoc]
    constructor
    · rintro ⟨h, -⟩
      exact h
    · intro h
      exact ⟨h, lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hq) h⟩

/-- Counting the entries `< M2` among those `< M1`, for `M2 ≤ M1`. -/
theorem countP_filter_of_le (S : Multiset ℕ) {M1 M2 : ℕ} (h : M2 ≤ M1) :
    (S.filter (· < M1)).countP (· < M2) = Multiset.card (S.filter (· < M2)) := by
  rw [Multiset.countP_eq_card_filter, Multiset.filter_filter]
  congr 2
  funext x
  apply propext
  constructor
  · rintro ⟨h2, -⟩; exact h2
  · intro h2; exact ⟨h2, lt_of_lt_of_le h2 h⟩

/-! ### Unweighted decomposition of the box -/

/-- **Recursive decomposition of the box** for arbitrary sums: for `q ∉ S`,
`Σ_{v ∈ box (insert q S)} f v = Σ_{a ≤ γ q} Σ_{w ∈ box S} f (update w q a)`. -/
theorem sum_box_insert {M : Type*} [AddCommMonoid M] {q : ℕ} {S : Finset ℕ} (hq : q ∉ S)
    (γ : ℕ → ℕ) (f : (ℕ → ℕ) → M) :
    ∑ v ∈ box (insert q S) γ, f v =
      ∑ a ∈ range (γ q + 1), ∑ w ∈ box S γ, f (Function.update w q a) := by
  rw [← sum_product' (range (γ q + 1)) (box S γ) (fun a w => f (Function.update w q a))]
  symm
  refine sum_nbij' (fun x => Function.update x.2 q x.1) (fun v => (v q, Function.update v q 0))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, w⟩ h
    rw [mem_product] at h
    exact update_mem_box_insert hq h.2 (Nat.lt_succ_iff.1 (mem_range.1 h.1))
  · intro v hv
    rw [mem_box] at hv
    rw [mem_product, mem_box]
    refine ⟨mem_range.2 (Nat.lt_succ_of_le (hv.1 q (mem_insert_self q S))),
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
    rfl

end MinModulus.CheckerSound.C
