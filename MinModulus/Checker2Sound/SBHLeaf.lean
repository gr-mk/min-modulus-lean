import MinModulus.Checker2Sound.SBHCode
import MinModulus.Checker2Math.SBHLaw
import MinModulus.CheckerMath.ImplBridge
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# `Checker2Sound.SBHLeaf` (agent L2-D): one DFS leaf of the S/B/H bound

STATUS: complete (fully proved; agent L2-D). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

* `leafValue_sound`: the code's `leafValue` (`corrSum` over the rows of one profile table) is an
  upper W-value of the leaf function `A.sbhLeaf R ν N a τ β ω = E_R[(τ T − β − ω b)⁺]`, given the
  facts about the table that `buildTab_sound` provides (`TabOK`), `E[T] ≤ wv ETW`, and lower
  bounds `wv (tp1 + F) ≤ β`, `wv om ≤ ω` (L2-A's `sbhLeaf_le`).
* the pattern facts at a leaf: `smallDivs` at the pattern index of a leaf `u` lists the divisors
  `d ∣ s_S(u)` with `d·p < m` (`smallDivs_leaf`), hence `wv (sumCd …) ≤ F(s_S(u))` and
  `profileOf … = (a_q(s_S(u)))_q`.
-/

namespace MinModulus.Checker2Sound.D

open MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.Checker2Math MinModulus.Smooth
  MinModulus.CheckerMath Finset

/-! ### Rounding facts for the leaf -/

theorem W48_real : ((W48 : ℕ) : ℝ) = 2 ^ 48 := by rw [W48_eq]; norm_num

theorem wv_W48 : wv W48 = 1 := by unfold wv; rw [W48_real]; norm_num

theorem floor_wv (x : ℕ) : ⌊wv x⌋₊ = x >>> 48 := by
  unfold wv
  rw [Nat.shiftRight_eq_div_pow]
  have h : ((2 : ℝ) ^ 48) = ((2 ^ 48 : ℕ) : ℝ) := by push_cast; ring
  rw [h]
  exact Nat.floor_div_eq_div (K := ℝ) x (2 ^ 48)

theorem wv_lt_one_iff (x : ℕ) : wv x < 1 ↔ x < W48 := by
  unfold wv
  rw [div_lt_one (by positivity), W48_eq]
  have h : ((2 : ℝ) ^ 48) = ((2 ^ 48 : ℕ) : ℝ) := by push_cast; ring
  rw [h, Nat.cast_lt]

theorem wv_cdiv_ge (x τ : ℕ) (hτ : 0 < τ) : wv x / τ ≤ wv (cdiv x τ) := by
  have h := cdiv_ge (a := x) hτ
  unfold wv
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right h (by positivity)

theorem wv_mulDn_le (om EbW : ℕ) : wv (mulDn (om <<< 14) EbW) ≤ wv om * wv EbW := by
  have h := Nat.cast_le (α := ℝ) |>.mpr (mulDn_spec (om <<< 14) EbW)
  generalize mulDn (om <<< 14) EbW = X at h ⊢
  rw [Nat.cast_mul, Nat.cast_mul, Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, ONE_real'] at h
  have h2 : (X : ℝ) * 2 ^ 62 ≤ (om : ℝ) * 2 ^ 14 * EbW := by
    simpa using h
  unfold wv
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem wv_mulUp_ge (cW s0 : ℕ) : wv cW * pv s0 ≤ wv (mulUp cW s0) := wv_mul_pv_le_mulUp cW s0

/-! ### One leaf -/

/-- What `buildTab_sound` provides for one profile table, in the form used at a leaf. -/
structure TabOK (R : Finset ℕ) (ν : ℕ → ℝ) (N : ℕ) (a : ℕ → ℕ) (tab : ProfTab) : Prop where
  bm : ∑ q ∈ R, a q ≤ tab.bm
  Eb : wv tab.EbW ≤ expect R ν (fun _ => N) (fun w => (bstat R a w : ℝ))
  rows : ∀ b, b ≤ tab.bm → ∀ c : ℝ, 0 ≤ c → ⌊c⌋₊ ≤ tab.K →
    ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * lawJoint R a ν (fun _ => N) j b ≤
      c * pv (tabS0 tab b ⌊c⌋₊) - wv (tabS1W tab b ⌊c⌋₊)

/-- A row of the lower-tail correction is bounded by the code's `corrTerm`. -/
theorem row_le_corrTerm {R : Finset ℕ} {ν : ℕ → ℝ} {N : ℕ} {a : ℕ → ℕ} {tab : ProfTab}
    (htab : TabOK R ν N a tab) (β0 om τ b : ℕ) (hb : b ≤ tab.bm)
    (hK : W48 ≤ cdiv (β0 + b * om) τ → cdiv (β0 + b * om) τ >>> 48 ≤ tab.K) :
    ∑ j ∈ range (⌊wv (cdiv (β0 + b * om) τ)⌋₊ + 1),
        (wv (cdiv (β0 + b * om) τ) - j) * lawJoint R a ν (fun _ => N) j b ≤
      wv (corrTerm tab β0 om τ b) := by
  set cW := cdiv (β0 + b * om) τ with hcW
  unfold corrTerm
  rw [← hcW]
  by_cases h1 : cW < W48
  · rw [ite_eq_left h1, A.lowerTail_row_eq_zero R a ν _ ((wv_lt_one_iff cW).2 h1) b]
    simp [wv]
  · rw [ite_eq_right h1]
    have hk : ⌊wv cW⌋₊ ≤ tab.K := by rw [floor_wv]; exact hK (not_lt.1 h1)
    have h2 := htab.rows b hb (wv cW) (wv_nonneg cW) hk
    rw [floor_wv] at h2 ⊢
    refine h2.trans ?_
    unfold tabS0 tabS1W
    refine le_trans ?_ (wv_sub_ge _ _)
    have := wv_mulUp_ge cW ((tab.S0[b]!)[cW >>> 48]!)
    linarith

/-- **One leaf** (`leafValue`): an upper W-value of `E_R[(τ T − β − ω b)⁺]`. -/
theorem leafValue_sound {R : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ R, 0 ≤ ν q ∧ ν q ≤ q) {N : ℕ}
    {a : ℕ → ℕ} {tab : ProfTab} (htab : TabOK R ν N a tab) {F τ ETW tp1 om : ℕ}
    (hτ : 0 < τ) (hET : expect R ν (fun _ => N) (fun w => (tauN R w : ℝ)) ≤ wv ETW)
    {β ω : ℝ} (hβ : wv (tp1 + F) ≤ β) (hω : wv om ≤ ω)
    (hok : (leafValue tab F τ ETW tp1 om (om <<< 14)).2 = true) :
    A.sbhLeaf R ν (fun _ => N) a τ β ω ≤ wv (leafValue tab F τ ETW tp1 om (om <<< 14)).1 := by
  unfold leafValue at hok ⊢
  simp only at hok ⊢
  obtain ⟨-, hK, hcorr⟩ := corrSum_spec tab (tp1 + F) om τ (tab.bm + 1) 0 0 true hok
  set corr := (corrSum tab (tp1 + F) om τ 0 (tab.bm + 1) 0 true).1 with hcorr_def
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  -- the lower-tail leaf bound of L2-A
  have hmain := A.sbhLeaf_le hν (fun _ => N) htab.bm (τ := (τ : ℝ)) (β' := wv (tp1 + F))
    (ω' := wv om) (ET := wv ETW) (Eb := wv tab.EbW) hτr hβ (wv_nonneg om) hω hET htab.Eb
    (fun b => wv (cdiv (tp1 + F + b * om) τ)) (fun b _ => by
      have := wv_cdiv_ge (tp1 + F + b * om) τ hτ
      rw [wv_add, wv_natMul, mul_comm (b : ℝ)] at this
      exact this)
  refine hmain.trans ?_
  -- the rows
  have hrows : ∑ b ∈ range (tab.bm + 1), ∑ j ∈ range (⌊wv (cdiv (tp1 + F + b * om) τ)⌋₊ + 1),
      (wv (cdiv (tp1 + F + b * om) τ) - j) * lawJoint R a ν (fun _ => N) j b ≤ wv corr := by
    rw [hcorr, zero_add, zero_add, ← range_eq_Ico, show wv (∑ b ∈ range (tab.bm + 1),
      corrTerm tab (tp1 + F) om τ b) = ∑ b ∈ range (tab.bm + 1), wv (corrTerm tab (tp1 + F) om τ b)
      by unfold wv; push_cast; rw [sum_div]]
    exact sum_le_sum fun b hb => row_le_corrTerm htab (tp1 + F) om τ b
      (Nat.lt_succ_iff.1 (mem_range.1 hb)) (hK b (Nat.zero_le b) (by simpa using mem_range.1 hb))
  have hmul := mul_le_mul_of_nonneg_left hrows hτr.le
  have hdn := wv_mulDn_le om tab.EbW
  have hsub := wv_sub_ge (τ * ETW + τ * corr) (tp1 + F + mulDn (om <<< 14) tab.EbW)
  rw [wv_add, wv_natMul, wv_natMul, wv_add (tp1 + F)] at hsub
  have homEb : wv om * wv tab.EbW ≥ wv (mulDn (om <<< 14) tab.EbW) := hdn
  linarith


/-! ### `c(d)`: `cdLoW` is a lower W-value -/

theorem cdLoW_le {m p d : ℕ} (hp : 1 < p) (hd : 0 < d) : wv (cdLoW m p d) ≤ cc p m d := by
  have hJ := j0m1_le (m := m) hp hd
  set e := j0m1 m p d with he
  set J := j0 p m d - 1 with hJdef
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpe : (0 : ℝ) < (p : ℝ) ^ e := pow_pos hp0 e
  have hpJ : (p : ℝ) ^ e ≤ (p : ℝ) ^ J :=
    pow_le_pow_right₀ (by exact_mod_cast hp.le) hJ
  have hcd := cdiv_ge (a := W48) (b := p ^ e) (pow_pos (by omega) e)
  push_cast at hcd
  unfold cdLoW cc
  rw [← he]
  have h1 : wv (W48 - cdiv W48 (p ^ e)) ≤ wv W48 - wv (cdiv W48 (p ^ e)) ∨
      W48 - cdiv W48 (p ^ e) = 0 := by
    rcases le_total (cdiv W48 (p ^ e)) W48 with h | h
    · left; unfold wv; rw [Nat.cast_sub h, sub_div]
    · right; omega
  have hinvJ : ((p : ℝ)⁻¹) ^ J = 1 / (p : ℝ) ^ J := by rw [inv_pow, one_div]
  have hle1 : 1 / (p : ℝ) ^ J ≤ 1 := by
    rw [div_le_one (pow_pos hp0 J)]; exact one_le_pow₀ (by exact_mod_cast hp.le)
  rcases h1 with h1 | h1
  · refine h1.trans ?_
    rw [wv_W48, hinvJ]
    have : 1 / (p : ℝ) ^ J ≤ wv (cdiv W48 (p ^ e)) := by
      unfold wv
      rw [W48_real] at hcd
      rw [le_div_iff₀ (by positivity)]
      calc 1 / (p : ℝ) ^ J * 2 ^ 48 ≤ 1 / (p : ℝ) ^ e * 2 ^ 48 := by
            gcongr
        _ = 2 ^ 48 / (p : ℝ) ^ e := by ring
        _ ≤ _ := hcd
    linarith
  · rw [h1, hinvJ]
    simp only [wv, Nat.cast_zero, zero_div]
    linarith

/-! ### The pattern of a leaf -/

section Pattern

variable {P : Params2}

theorem extract0_size {n : ℕ} (hn : n ≤ (primes2 P).size) :
    ((primes2 P).extract 0 n).size = n := by
  rw [size_extract']; omega

theorem extract0_get {n i : ℕ} (hn : n ≤ (primes2 P).size) (hi : i < n) :
    ((primes2 P).extract 0 n)[i]! = (primes2 P)[i]! := by
  rw [getElem!_extract _ (by omega), zero_add]

theorem idxSet_zero_eq_image {n : ℕ} (hn : n ≤ (primes2 P).size) :
    idxSet P 0 n = (range n).image (fun i => (primes2 P)[i]!) := by
  ext q
  rw [mem_idxSet, mem_image]
  constructor
  · rintro ⟨i, -, hi, -, rfl⟩; exact ⟨i, mem_range.2 hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, Nat.zero_le i, mem_range.1 hi, by simp at hi; omega, rfl⟩

theorem smooth_idxSet_zero {n : ℕ} (hn : n ≤ (primes2 P).size) (w : ℕ → ℕ) :
    smooth (idxSet P 0 n) w = ∏ i ∈ range n, (primes2 P)[i]! ^ w ((primes2 P)[i]!) := by
  unfold smooth
  rw [idxSet_zero_eq_image hn, prod_image]
  intro i hi j hj hij
  exact primes2_inj (by simp at hi; omega) (by simp at hj; omega) hij

/-- **`smallDivs` at a leaf.** For a leaf `u` of the DFS (exponents `u q ≤ 60` on `S = primes[0:n]`),
`smallDivs` at the pattern index of `u` lists, without repetition, the divisors `d ∣ s_S(u)` with
`d·p < m` (small patterns: `F` and the profile only see `min (u q) kk_q`). -/
theorem smallDivs_leaf {n : ℕ} (hn : n ≤ (primes2 P).size) {m p : ℕ} (hp : 0 < p)
    (hN1 : 1 < cdiv m p) {u : ℕ → ℕ} (hu : ∀ i < n, u ((primes2 P)[i]!) ≤ 60) :
    let Sq := (primes2 P).extract 0 n
    let kk := Sq.map (kkOf · (cdiv m p))
    let pat := ∑ i ∈ range n, min (u ((primes2 P)[i]!)) (kkOf ((primes2 P)[i]!) (cdiv m p)) *
      sprod kk i
    (smallDivs Sq kk (cdiv m p) pat).toList.Nodup ∧
      ∀ x, x ∈ (smallDivs Sq kk (cdiv m p) pat).toList ↔ x ∣ smooth (idxSet P 0 n) u ∧ x * p < m := by
  intro Sq kk pat
  set N1 := cdiv m p with hN1def
  have hSqs : Sq.size = n := extract0_size hn
  have hSq : ∀ i < n, Sq[i]! = (primes2 P)[i]! := fun i hi => extract0_get hn hi
  have hkk : ∀ i < n, kk[i]! = kkOf ((primes2 P)[i]!) N1 := fun i hi => by
    simp only [kk]; rw [getElem!_map _ _ (by omega), hSq i hi]
  set e : ℕ → ℕ := fun i => min (u ((primes2 P)[i]!)) (kkOf ((primes2 P)[i]!) N1) with he
  have hpat : pat = ∑ i ∈ range Sq.size, e i * sprod kk i := by rw [hSqs]
  have hpr : ∀ i < Sq.size, (Sq[i]!).Prime := fun i hi => by
    rw [hSq i (by omega)]; exact primes2_prime (by omega)
  have hinj : ∀ i j, i < Sq.size → j < Sq.size → Sq[i]! = Sq[j]! → i = j := by
    intro i j hi hj h
    rw [hSq i (by omega), hSq j (by omega)] at h
    exact primes2_inj (by omega) (by omega) h
  have he' : ∀ i < Sq.size, e i ≤ kk[i]! := fun i hi => by
    rw [hkk i (by omega)]; exact min_le_right _ _
  obtain ⟨hnd, hmem⟩ := smallDivs_spec (N1 := N1) hpr hinj he' hN1
  rw [hpat]
  refine ⟨hnd, fun x => ?_⟩
  rw [hmem x, hSqs]
  -- `npart` is `s_S` of the truncated exponents
  set w : ℕ → ℕ := fun q => min (u q) (kkOf q N1) with hw
  have hnp : npart Sq e n = smooth (idxSet P 0 n) w := by
    rw [smooth_idxSet_zero hn]
    unfold npart
    exact prod_congr rfl fun i hi => by rw [hSq i (mem_range.1 hi)]
  rw [hnp]
  have hS : ∀ q ∈ idxSet P 0 n, q.Prime := fun q hq => idxSet_prime hq
  let K : ℕ → ℕ := fun q => if kkOf q N1 < 64 then kkOf q N1 else m
  have hK : ∀ q ∈ idxSet P 0 n, m ≤ q ^ (K q + 1) * p := by
    intro q hq
    have hq2 := (hS q hq).two_le
    simp only [K]
    split_ifs with h
    · have h1 := le_pow_kkOf (q := q) (N1 := N1) h
      calc m ≤ N1 * p := le_cdiv_mul m p hp
        _ ≤ q ^ (kkOf q N1 + 1) * p := Nat.mul_le_mul_right p h1
    · calc m ≤ 2 ^ m := (Nat.lt_two_pow_self).le
        _ ≤ q ^ (m + 1) := (Nat.pow_le_pow_left hq2 m).trans (Nat.pow_le_pow_right (by omega) (by omega))
        _ ≤ q ^ (m + 1) * p := Nat.le_mul_of_pos_right _ hp
  have hvw : ∀ q ∈ idxSet P 0 n, min (u q) (K q) = min (w q) (K q) := by
    intro q hq
    obtain ⟨i, -, hi, -, rfl⟩ := mem_idxSet.1 hq
    simp only [K, w]
    split_ifs with h
    · rw [min_assoc, min_self]
    · have h64 : kkOf ((primes2 P)[i]!) N1 = 64 := le_antisymm (kkOf_le _ _) (not_lt.1 h)
      rw [h64, min_eq_left (show u ((primes2 P)[i]!) ≤ 64 by have := hu i hi; omega)]
  have hfilt := filter_divisors_congr_small hS hK hvw
  have e1 : x ∣ smooth (idxSet P 0 n) w ∧ x < N1 ↔
      x ∈ (smooth (idxSet P 0 n) w).divisors.filter (fun d => d * p < m) := by
    rw [mem_filter, Nat.mem_divisors, lt_cdiv_iff hp]
    have hpos : ∀ q ∈ idxSet P 0 n, 0 < q := fun q hq => (hS q hq).pos
    exact ⟨fun h => ⟨⟨h.1, smooth_ne_zero hpos w⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  have e2 : x ∣ smooth (idxSet P 0 n) u ∧ x * p < m ↔
      x ∈ (smooth (idxSet P 0 n) u).divisors.filter (fun d => d * p < m) := by
    rw [mem_filter, Nat.mem_divisors]
    have hpos : ∀ q ∈ idxSet P 0 n, 0 < q := fun q hq => (hS q hq).pos
    exact ⟨fun h => ⟨⟨h.1, smooth_ne_zero hpos u⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [e1, e2, hfilt]

end Pattern


/-! ### `F` and the profile from the small divisors -/

theorem wv_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) : wv (∑ i ∈ s, f i) = ∑ i ∈ s, wv (f i) := by
  unfold wv; rw [Nat.cast_sum, sum_div]

/-- `sumCd` over the small divisors is a lower W-value of `F(n) = Σ_{d ∣ n, d·p < m} c(d)`. -/
theorem sumCd_le_Fsum {m p : ℕ} (hp : 1 < p) {n : ℕ} (hn : n ≠ 0) {ds : Array ℕ}
    (hnd : ds.toList.Nodup) (hmem : ∀ x, x ∈ ds.toList ↔ x ∣ n ∧ x * p < m) :
    wv (sumCd (cdTable m p (cdiv m p)) ds) ≤ Fsum p m n := by
  rw [sumCd_eq]
  have hfin : ds.toList.toFinset = n.divisors.filter (fun d => d * p < m) := by
    ext x
    rw [List.mem_toFinset, hmem, mem_filter, Nat.mem_divisors]
    exact ⟨fun h => ⟨⟨h.1, hn⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [← List.sum_toFinset _ hnd, hfin, wv_sum]
  unfold Fsum
  refine sum_le_sum fun d hd => ?_
  rw [mem_filter, Nat.mem_divisors] at hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hn)
  rw [cdTable_get m p (cdiv m p) ((lt_cdiv_iff (by omega)).2 hd.2)]
  exact cdLoW_le hp hd0

/-- The profile computed from the small divisors of `n`: `a_q(n)` at every `q ∈ Bq`, `0` off `Bq`. -/
theorem profileFn_profileOf {Bq ds : Array ℕ} {m p : ℕ} (hp : 0 < p)
    (hBq : ∀ q ∈ Bq.toList, 0 < q) {n : ℕ} (hn : n ≠ 0)
    (hnd : ds.toList.Nodup) (hmem : ∀ x, x ∈ ds.toList ↔ x ∣ n ∧ x * p < m) (q : ℕ) :
    profileFn Bq (profileOf Bq ds (cdiv m p)) q =
      if q ∈ Bq.toList.toFinset then acount p m q n else 0 := by
  unfold profileFn
  by_cases hq : q ∈ Bq.toList
  · rw [ite_eq_left (List.mem_toFinset.2 hq)]
    have hidx : Bq.toList.idxOf q < Bq.size := by
      have := List.idxOf_lt_length_iff.2 hq; simpa using this
    have hget : Bq[Bq.toList.idxOf q]! = q := by
      rw [← getElem_toList_eq_getElem! Bq (by simpa using hidx), List.getElem_idxOf]
    rw [profileOf_get _ _ _ hidx, hget]
    have hq0 : 0 < q := hBq q hq
    rw [← List.toFinset_card_of_nodup (hnd.filter _), List.toFinset_filter]
    unfold acount
    congr 1
    ext x
    rw [mem_filter, mem_filter, List.mem_toFinset, hmem, Nat.mem_divisors, decide_eq_true_eq,
      lt_cdiv_iff hp]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h1, hn⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      refine ⟨⟨h1, lt_of_le_of_lt ?_ h2⟩, h2⟩
      exact Nat.mul_le_mul_right p (Nat.le_mul_of_pos_right x hq0)
  · rw [ite_eq_right (fun h => hq (List.mem_toFinset.1 h)), List.idxOf_eq_length hq]
    rw [getElem!_of_size_le' _ (by rw [profileOf_size]; simp)]
    rfl

end MinModulus.Checker2Sound.D
