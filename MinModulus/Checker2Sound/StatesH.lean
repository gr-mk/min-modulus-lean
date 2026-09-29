import MinModulus.Checker2Sound.PrimsReal

/-!
# `Checker2Sound.StatesH` (agent L2-C): the `T_H` state (`HValid_init`, `HValid_extend`)

STATUS: complete, no `sorry` (agent L2-C, lean2 stage 2). Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

* generic real forms of the DP primitive: `pv_dpRange_ge` (push form) and `sum_push_eq_pull`
  (`Σ_{1≤t≤K} [t(a+1) = T] X t = [(a+1) ∣ T] X (T/(a+1))`), `pv_dpRange_zeros_ge_pull`;
* `HLaw P S D E`: the law part of `HValid` for an arbitrary set `S` of primes; `HLaw_step` (one
  `lawStepFull` step, math: `TauLaw.lawTau_insert`, `rho_eq_pointMass`), `HLaw_addRange`
  (the loop `HState.addRange`);
* **`HValid_init`**, **`HValid_extend`** (the statements of `Checker2Sound/Interfaces.lean`).
-/

namespace MinModulus.Checker2Sound.C

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Main MinModulus.Smooth MinModulus.Checker2Sound

/-! ### The DP primitive in real terms -/

/-- **`dpRange`, real push form**: `pv Dn[T] + Σ_{1 ≤ t ≤ K} Σ_{alo ≤ a < ahi} [t(a+1) = T]
pv D[t]·pv pm[a] ≤ pv Dn'[T]` (for `T ≤ K < Dn.size`). -/
theorem pv_dpRange_ge (Dn D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) (hK : K < Dn.size)
    {T : ℕ} (hT : T ≤ K) :
    pv Dn[T]! + ∑ t ∈ Ico 1 (K + 1), ∑ a ∈ Ico alo ahi,
        (if t * (a + 1) = T then pv D[t]! * pv pm[a]! else 0) ≤
      pv (dpRange Dn D K pm alo ahi)[T]! := by
  rw [dpRange_get Dn D K pm alo ahi hK hT, pv_add, pv_sum]
  refine add_le_add le_rfl (sum_le_sum fun t _ => ?_)
  rw [pv_sum]
  refine sum_le_sum fun a _ => ?_
  rw [pv_ite]
  split_ifs
  · exact pv_mulUp _ _
  · exact le_rfl

/-- Push ↔ pull: for `1 ≤ T ≤ K`, `Σ_{1 ≤ t ≤ K} [t (a+1) = T] X t = [(a+1) ∣ T] X (T/(a+1))`. -/
theorem sum_push_eq_pull {K T : ℕ} (hT1 : 1 ≤ T) (hT : T ≤ K) (a : ℕ) (X : ℕ → ℝ) :
    ∑ t ∈ Ico 1 (K + 1), (if t * (a + 1) = T then X t else 0) =
      if (a + 1) ∣ T then X (T / (a + 1)) else 0 := by
  rw [← sum_mul_succ_eq hT a X, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < K + 1),
    ite_eq_right (by omega), zero_add]

/-- **`dpRange` on a zero array, real pull form**: for `1 ≤ T ≤ K`,
`Σ_{alo ≤ a < ahi} [(a+1) ∣ T] pv D[T/(a+1)]·pv pm[a] ≤ pv new[T]`. -/
theorem pv_dpRange_zeros_ge_pull (D : Array ℕ) (K : ℕ) (pm : Array ℕ) (alo ahi : ℕ) {T : ℕ}
    (hT1 : 1 ≤ T) (hT : T ≤ K) :
    ∑ a ∈ Ico alo ahi, (if (a + 1) ∣ T then pv D[T / (a + 1)]! * pv pm[a]! else 0) ≤
      pv (dpRange (zeros (K + 1)) D K pm alo ahi)[T]! := by
  have h := pv_dpRange_ge (zeros (K + 1)) D K pm alo ahi (by rw [size_zeros]; omega) hT
  rw [aget_zeros, pv_zero, zero_add, sum_comm] at h
  refine le_of_eq_of_le (sum_congr rfl fun a _ => ?_) h
  rw [sum_push_eq_pull hT1 hT a (fun t => pv D[t]! * pv pm[a]!)]

/-! ### Laws of `τ` -/

theorem lawTau_zero (S : Finset ℕ) (ν : ℕ → ℝ) (γ : ℕ → ℕ) : lawTau S ν γ 0 = 0 := by
  unfold lawTau
  refine (expect_congr_fun (g := fun _ => (0 : ℝ)) fun v _ => ?_).trans (expect_const S ν γ 0)
  rw [ite_eq_right (tauN_pos S v).ne']

theorem lawTau_nonneg {S : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ)
    (T : ℕ) : 0 ≤ lawTau S ν γ T :=
  expect_nonneg hν fun v _ => by split_ifs <;> norm_num

/-! ### The `T_H` law for an arbitrary set of primes -/

/-- The law part of `HValid` for an arbitrary set `S` of primes (`D` holds upper bounds of the law of
`T_S` on `[0, KH]`, `E` an upper bound of `∏_S (1 + ν/(q−1)) ≥ E[T_S]`). -/
structure HLaw (P : Params2) (S : Finset ℕ) (D : Array ℕ) (E : ℕ) : Prop where
  mem : ∀ q ∈ S, q.Prime ∧ q ≤ P.X
  size : D.size = P.KH + 1
  law : ∀ N, P.KH ≤ N → ∀ k, k ≤ P.KH → lawTau S (nu2 P) (fun _ => N) k ≤ pv D[k]!
  mean : ∏ q ∈ S, (1 + nu2 P q / ((q : ℝ) - 1)) ≤ pv E

theorem nu2_mem_of {P : Params2} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime ∧ q ≤ P.X) :
    ∀ q ∈ S, 0 ≤ nu2 P q ∧ nu2 P q ≤ q :=
  fun q hq => nu2_mem (hS q hq).1.two_le (hS q hq).2

/-- **One `T_H` step** (`lawStepFull` with `pmArr q dn (KH − 1)`, `E ← mulUp E (facE1u q dn)`). -/
theorem HLaw_step {P : Params2} {S : Finset ℕ} {D : Array ℕ} {E : ℕ} (h : HLaw P S D E) {q : ℕ}
    (hq : q.Prime) (hqX : q ≤ P.X) (hqS : q ∉ S) :
    HLaw P (insert q S) (lawStepFull D P.KH (pmArr q (deltaN2 P q) (P.KH - 1)))
      (mulUp E (facE1u q (deltaN2 P q))) := by
  have hq2 := hq.two_le
  have hν : ∀ r ∈ S, 0 ≤ nu2 P r ∧ nu2 P r ≤ r := nu2_mem_of h.mem
  have hνq := nu2_mem hq2 hqX
  refine ⟨fun r hr => ?_, ?_, fun N hN k hk => ?_, ?_⟩
  · rcases mem_insert.1 hr with rfl | hr
    · exact ⟨hq, hqX⟩
    · exact h.mem r hr
  · unfold lawStepFull
    rw [dpRange_zeros_size]
  · -- the law
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [lawTau_zero]
      exact pv_nonneg _
    rw [lawTau_insert hqS]
    -- only `a < KH` contributes (`(a+1) ∣ k`, `1 ≤ k ≤ KH`)
    rw [sum_range_eq_of_vanish (n := P.KH) (by omega) fun a ha _ => by
      rw [ite_eq_right fun hd => absurd (Nat.le_of_dvd hk1 hd) (by omega)]]
    unfold lawStepFull
    refine le_trans ?_ (pv_dpRange_zeros_ge_pull D P.KH _ 0 P.KH hk1 hk)
    rw [range_eq_Ico]
    refine sum_le_sum fun a ha => ?_
    have ha' : a < P.KH := (mem_Ico.1 ha).2
    split_ifs with hd
    · have hkd : k / (a + 1) ≤ P.KH := (Nat.div_le_self k (a + 1)).trans hk
      have h1 := h.law N hN (k / (a + 1)) hkd
      have h2 : rho q (nu2 P q) N a ≤ pv (pmArr q (deltaN2 P q) (P.KH - 1))[a]! := by
        rw [nu2_eq_tiltN hqX]
        exact rho_le_pmArr hq2 (two_deltaN2_le P q) (by omega) (by omega)
      exact mul_le_mul h1 h2 (rho_nonneg hνq.1 hνq.2 _ _)
        ((lawTau_nonneg hν _ _).trans h1)
    · exact le_rfl
  · -- the mean
    rw [prod_insert hqS]
    have h1 : 1 + nu2 P q / ((q : ℝ) - 1) ≤ pv (facE1u q (deltaN2 P q)) := by
      rw [nu2_eq_tiltN hqX]
      exact facE1u_ge hq2 (deltaN2_lt P q)
    have h0 : 0 ≤ ∏ r ∈ S, (1 + nu2 P r / ((r : ℝ) - 1)) := by
      refine prod_nonneg fun r hr => ?_
      have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (h.mem r hr).1.two_le
      have := (hν r hr).1
      have : 0 ≤ nu2 P r / ((r : ℝ) - 1) := div_nonneg this (by linarith)
      linarith
    have hq1 : (0 : ℝ) ≤ 1 + nu2 P q / ((q : ℝ) - 1) := by
      have hr2 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
      have : 0 ≤ nu2 P q / ((q : ℝ) - 1) := div_nonneg hνq.1 (by linarith)
      linarith
    calc (1 + nu2 P q / ((q : ℝ) - 1)) * ∏ r ∈ S, (1 + nu2 P r / ((r : ℝ) - 1))
        ≤ pv (facE1u q (deltaN2 P q)) * pv E := mul_le_mul h1 h.mean h0 (hq1.trans h1)
      _ = pv E * pv (facE1u q (deltaN2 P q)) := mul_comm _ _
      _ ≤ pv (mulUp E (facE1u q (deltaN2 P q))) := pv_mulUp _ _

theorem dns2_get {P : Params2} {i : ℕ} (hi : i < (primes2 P).size) :
    (dns2 P)[i]! = deltaN2 P (primes2 P)[i]! := by
  unfold dns2
  exact aget_map _ _ hi

theorem primes2_get_mem {P : Params2} (hPX : P.PX ≤ P.X) {i : ℕ} (hi : i < (primes2 P).size) :
    (primes2 P)[i]!.Prime ∧ (primes2 P)[i]! ≤ P.X := by
  have hi' : i < (primes2 P).toList.length := by simpa using hi
  rw [aget_eq_list hi']
  have := primes2_mem (List.getElem_mem hi')
  exact ⟨this.1, this.2.trans hPX⟩

theorem idxSet_succ_left (P : Params2) {lo hi : ℕ} (hlh : lo < hi) (hs : lo < (primes2 P).size) :
    idxSet P lo hi = insert (primes2 P)[lo]! (idxSet P (lo + 1) hi) := by
  ext x
  rw [mem_insert, mem_idxSet, mem_idxSet]
  constructor
  · rintro ⟨i, h1, h2, h3, rfl⟩
    by_cases hil : i = lo
    · subst hil; exact Or.inl rfl
    · exact Or.inr ⟨i, by omega, h2, h3, rfl⟩
  · rintro (rfl | ⟨i, h1, h2, h3, rfl⟩)
    · exact ⟨lo, le_rfl, hlh, hs, rfl⟩
    · exact ⟨i, by omega, h2, h3, rfl⟩

theorem idxSet_union (P : Params2) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    idxSet P a b ∪ idxSet P b c = idxSet P a c := by
  ext x
  rw [mem_union, mem_idxSet, mem_idxSet, mem_idxSet]
  constructor
  · rintro (⟨i, h1, h2, h3, rfl⟩ | ⟨i, h1, h2, h3, rfl⟩)
    · exact ⟨i, h1, by omega, h3, rfl⟩
    · exact ⟨i, by omega, h2, h3, rfl⟩
  · rintro ⟨i, h1, h2, h3, rfl⟩
    by_cases hib : i < b
    · exact Or.inl ⟨i, h1, hib, h3, rfl⟩
    · exact Or.inr ⟨i, by omega, h2, h3, rfl⟩

/-- **The loop `HState.addRange`**: adding the primes of index `[i, i + f)` (none of them in `S`). -/
theorem HLaw_addRange {P : Params2} (hPX : P.PX ≤ P.X) :
    ∀ (f i : ℕ) (S : Finset ℕ) (D : Array ℕ) (E : ℕ), HLaw P S D E → i + f ≤ (primes2 P).size →
      (∀ j, i ≤ j → j < i + f → (primes2 P)[j]! ∉ S) →
      HLaw P (S ∪ idxSet P i (i + f)) (HState.addRange (primes2 P) (dns2 P) P.KH D E i f).1
        (HState.addRange (primes2 P) (dns2 P) P.KH D E i f).2 := by
  intro f
  induction f with
  | zero =>
    intro i S D E h _ _
    rw [Nat.add_zero, idxSet_self, union_empty]
    exact h
  | succ f ih =>
    intro i S D E h hs hS
    rw [HState.addRange.eq_2]
    have hi : i < (primes2 P).size := by omega
    have hmem := primes2_get_mem hPX hi
    rw [dns2_get hi]
    have h1 := HLaw_step h hmem.1 hmem.2 (hS i le_rfl (by omega))
    have h2 := ih (i + 1) _ _ _ h1 (by omega) (fun j hj1 hj2 => by
      rw [mem_insert, not_or]
      refine ⟨fun he => ?_, hS j (by omega) (by omega)⟩
      have := primes2_inj (by omega) hi he
      omega)
    have e : insert (primes2 P)[i]! S ∪ idxSet P (i + 1) (i + 1 + f) =
        S ∪ idxSet P i (i + (f + 1)) := by
      rw [idxSet_succ_left P (by omega : i < i + (f + 1)) hi, show i + 1 + f = i + (f + 1) by omega,
        insert_union, union_insert]
    rw [e] at h2
    exact h2

/-- `HValid` is `HLaw` for the set `idxSet P H.lo H.hi` plus the index bounds. -/
theorem HLaw_of_HValid {P : Params2} (hPX : P.PX ≤ P.X) {H : HState} (hH : HValid P H) :
    HLaw P (idxSet P H.lo H.hi) H.D H.E :=
  ⟨fun _ hq => ⟨(idxSet_mem hq).1, (idxSet_mem hq).2.trans hPX⟩, hH.size, hH.law, hH.mean⟩

/-! ### The two statements -/

/-- **(L2-C)** The empty `T_H` state. -/
theorem HValid_init (P : Params2) (hKH : 1 ≤ P.KH) : HValid P (HState.init P.KH) := by
  refine ⟨⟨le_rfl, Nat.zero_le _⟩, ?_, fun N _ k _ => ?_, ?_⟩
  · unfold HState.init
    simp only
    rw [size_set, size_zeros]
  · unfold HState.init
    simp only
    rw [idxSet_self, lawTau_empty, aget_set, size_zeros]
    by_cases hk : k = 1
    · subst hk
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, by omega⟩, pv_ONE2]
    · rw [ite_eq_right hk, ite_eq_right (fun h => hk h.1.symm), aget_zeros, pv_zero]
  · unfold HState.init
    simp only
    rw [idxSet_self, prod_empty, pv_ONE2]

/-- **(L2-C)** `HState.extend` makes `H = primes2 P [iN1:k]` (code: `HState.addRange`,
`lawStepFull`, `pmArr`, `facE1u`; math: `TauLaw.lawTau_insert`, `rho_eq_pointMass`). -/
theorem HValid_extend (P : Params2) (hPX : P.PX ≤ P.X) {H : HState} (hH : HValid P H) {iN1 k : ℕ}
    (hk : k ≤ (primes2 P).size) (hiN1 : iN1 < k)
    (hok : (H.extend (primes2 P) (dns2 P) P.KH iN1 k).2 = true) :
    HValid P (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1 ∧
      (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1.lo = iN1 ∧
      (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1.hi = k := by
  have hL := HLaw_of_HValid hPX hH
  unfold HState.extend at hok ⊢
  rw [ite_eq_right (by omega)] at hok ⊢
  by_cases hLH : H.lo = H.hi
  · -- empty `H`: `lo = hi = iN1`
    have hb : (H.lo == H.hi) = true := by simp [hLH]
    simp only [hb, ite_true, Nat.sub_self] at hok ⊢
    rw [HState.addRange.eq_1]
    simp only
    have hS : idxSet P H.lo H.hi = ∅ := by rw [hLH, idxSet_self]
    rw [hS] at hL
    have h := HLaw_addRange hPX (k - iN1) iN1 ∅ H.D H.E hL (by omega)
      (fun j _ _ => notMem_empty _)
    rw [empty_union, show iN1 + (k - iN1) = k by omega] at h
    exact ⟨⟨⟨hiN1.le, hk⟩, h.size, h.law, h.mean⟩, by trivial, by trivial⟩
  · -- nonempty `H`: `iN1 ≤ lo ≤ hi ≤ k`
    have hb : (H.lo == H.hi) = false := by simp [hLH]
    simp only [hb, Bool.false_eq_true, ite_false] at hok ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨h1, h2⟩ := hok
    have hlh := hH.idx.1
    have hA := HLaw_addRange hPX (H.lo - iN1) iN1 _ H.D H.E hL (by omega)
      (fun j _ hj => getElem_notMem_idxSet (by omega) (by omega))
    rw [show iN1 + (H.lo - iN1) = H.lo by omega] at hA
    have hB := HLaw_addRange hPX (k - H.hi) H.hi _ _ _ hA (by omega)
      (fun j hj _ => by
        rw [mem_union, not_or]
        exact ⟨getElem_notMem_idxSet (by omega) (by omega),
          getElem_notMem_idxSet (by omega) (by omega)⟩)
    rw [show H.hi + (k - H.hi) = k by omega] at hB
    have e : idxSet P H.lo H.hi ∪ idxSet P iN1 H.lo ∪ idxSet P H.hi k = idxSet P iN1 k := by
      rw [union_comm (idxSet P H.lo H.hi), idxSet_union P h1 hlh, idxSet_union P (by omega) h2]
    rw [e] at hB
    exact ⟨⟨⟨hiN1.le, hk⟩, hB.size, hB.law, hB.mean⟩, by trivial, by trivial⟩

end MinModulus.Checker2Sound.C
