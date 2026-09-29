import MinModulus.CheckerSound.EnumSem
import MinModulus.CheckerSound.Defs

/-!
# `CheckerSound.EnumPat` (agent CS-C): the leaf probabilities `C[pat]/s` (`patternConsts`)

Status: complete, no `sorry`.

`patternConsts aps adns = (bits, cup, clo)`:
* `mkBits_spec`: `bits[j] = 0` if `adns[j] = 0`, else `2^(kf j)` with `kf j` = the number of
  tilted A-primes of index `< j`; the number of tilted primes is `nt = kf n`;
* `testBit_patOf`, `patOf_lt`: the pattern of a configuration `w` (`patOf`, the `OR` of the
  `bits[j]` with `w q_j ≥ 1`) has bit `kf j` set iff `w q_j ≥ 1` (tilted `j`), and is `< 2^nt`;
  hence `pat &&& bits[j] ≠ 0 ↔ w q_j ≥ 1` (`and_bits_ne_zero_iff`);
* `numDen_spec`, `mkC_spec`: `cup[pat] = ⌈2^62 num/den⌉`, `clo[pat] = ⌊2^62 num/den⌋` with the
  exact products `num/den = C[pat]`;
* **`leaf_prob_bounds`**: for a configuration `w` below the caps,
  `⌊clo[pat]/s⌋ / 2^62 ≤ π(w) ≤ ⌈cup[pat]/s⌉ / 2^62` (`pat = patOf cfg 0 w`, `s = s(w)`), via
  `CheckerMath.weight_eq_div_smooth` and exact tilts `ν_q = 10^9/(10^9 - dn_q)`.
-/

namespace MinModulus.CheckerSound.C

open MinModulus.CheckerImpl MinModulus.Smooth Finset

/-! ### `push` -/

theorem getD0_push (a : Array ℕ) (x j : ℕ) :
    getD0 (a.push x) j = if j = a.size then x else getD0 a j := by
  rw [getD0_eq, getD0_eq, Array.getElem?_push]
  split_ifs <;> rfl

/-! ### `mkBits` -/

/-- The number of tilted A-primes (`adns[j'] ≠ 0`) of index `< j`. -/
def kf (adns : Array ℕ) (j : ℕ) : ℕ := ((range j).filter (fun j' => adns[j']! ≠ 0)).card

theorem kf_succ (adns : Array ℕ) (j : ℕ) :
    kf adns (j + 1) = kf adns j + if adns[j]! = 0 then 0 else 1 := by
  unfold kf
  rw [range_add_one, filter_insert]
  by_cases h : adns[j]! = 0
  · rw [ite_eq_right (not_not.2 h), ite_eq_left h, Nat.add_zero]
  · rw [ite_eq_left h, card_insert_of_notMem (by simp), ite_eq_right h]

theorem kf_mono (adns : Array ℕ) {j j' : ℕ} (h : j ≤ j') : kf adns j ≤ kf adns j' :=
  card_le_card (filter_subset_filter _ (range_mono h))

/-- A tilted index counts itself: `kf j < kf j'` for `j < j'`, `adns[j] ≠ 0`. -/
theorem kf_lt (adns : Array ℕ) {j j' : ℕ} (h : j < j') (hj : adns[j]! ≠ 0) :
    kf adns j < kf adns j' := by
  have h1 := kf_succ adns j
  rw [ite_eq_right hj] at h1
  have := kf_mono adns (show j + 1 ≤ j' by omega)
  omega

theorem kf_inj (adns : Array ℕ) {j j' : ℕ} (hj : adns[j]! ≠ 0) (hj' : adns[j']! ≠ 0)
    (h : kf adns j = kf adns j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd h (kf_lt adns hlt hj).ne
  · exact heq
  · exact absurd h.symm (kf_lt adns hgt hj').ne

theorem mkBits_spec (adns : Array ℕ) : ∀ f i (bits : Array ℕ), bits.size = i →
    (patternConsts.mkBits adns i (kf adns i) bits f).2 = kf adns (i + f) ∧
    (patternConsts.mkBits adns i (kf adns i) bits f).1.size = i + f ∧
    ∀ j, getD0 (patternConsts.mkBits adns i (kf adns i) bits f).1 j =
      if j < i then getD0 bits j
      else if j < i + f then (if adns[j]! = 0 then 0 else 2 ^ kf adns j) else 0 := by
  intro f
  induction f with
  | zero =>
    intro i bits hsize
    refine ⟨rfl, hsize, fun j => ?_⟩
    show getD0 bits j = _
    by_cases h1 : j < i
    · rw [ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]
      exact getD0_of_size_le (by omega)
  | succ f ih =>
    intro i bits hsize
    rw [patternConsts.mkBits]
    by_cases h0 : adns[i]! = 0
    · have hc : (adns[i]! == 0) = true := by simp [h0]
      rw [ite_eq_left hc]
      have hk : kf adns (i + 1) = kf adns i := by rw [kf_succ, ite_eq_left h0, Nat.add_zero]
      obtain ⟨h1, h2, h3⟩ := ih (i + 1) (bits.push 0) (by simp [hsize])
      rw [hk] at h1 h2 h3
      refine ⟨by rw [h1]; congr 1; omega, by rw [h2]; omega, fun j => ?_⟩
      rw [h3 j, getD0_push, hsize]
      split_ifs <;> first | rfl | omega | (subst_vars; simp_all)
    · have hc : ¬ (adns[i]! == 0) = true := by simp [h0]
      rw [ite_eq_right hc]
      have hk : kf adns (i + 1) = kf adns i + 1 := by rw [kf_succ, ite_eq_right h0]
      obtain ⟨h1, h2, h3⟩ := ih (i + 1) (bits.push (1 <<< kf adns i)) (by simp [hsize])
      rw [hk] at h1 h2 h3
      refine ⟨by rw [h1]; congr 1; omega, by rw [h2]; omega, fun j => ?_⟩
      rw [h3 j, getD0_push, hsize]
      split_ifs <;> first | rfl | omega | (subst_vars; simp_all [Nat.one_shiftLeft])

/-- The `bits` array of `patternConsts`. -/
theorem patternConsts_bits (aps adns : Array ℕ) :
    (patternConsts aps adns).1 = (patternConsts.mkBits adns 0 0 #[] aps.size).1 := by
  unfold patternConsts
  rfl

theorem getD0_bits (aps adns : Array ℕ) (j : ℕ) :
    getD0 (patternConsts aps adns).1 j =
      if j < aps.size then (if adns[j]! = 0 then 0 else 2 ^ kf adns j) else 0 := by
  rw [patternConsts_bits]
  have h := (mkBits_spec adns aps.size 0 #[] rfl).2.2 j
  simp only [kf, range_zero, filter_empty, card_empty, Nat.zero_add] at h
  simp only [kf]
  rw [h]
  simp

theorem mkBits_nt (aps adns : Array ℕ) :
    (patternConsts.mkBits adns 0 0 #[] aps.size).2 = kf adns aps.size := by
  have h := (mkBits_spec adns aps.size 0 #[] rfl).1
  simp only [Nat.zero_add] at h
  exact h

/-! ### The pattern of a configuration -/

theorem and_two_pow_eq (x k : ℕ) : x &&& 2 ^ k = if x.testBit k then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  split_ifs with h
  · rw [Nat.testBit_two_pow]
    by_cases hki : k = i
    · subst hki; simp [h]
    · simp [hki]
  · simp only [Nat.zero_testBit]
    by_cases hki : k = i
    · subst hki; simp [h]
    · simp [hki]

section
variable {cfg : EnumCfg}

/-- The bits of `patAux`: bit `k` is set iff some index `j` of the range with `w q_j ≥ 1` has
bit `k` set in `bits[j]`. -/
theorem testBit_patAux (w : ℕ → ℕ) (k : ℕ) : ∀ f i, (patAux cfg w i f).testBit k = true ↔
    ∃ j, i ≤ j ∧ j < i + f ∧ 1 ≤ w (qf cfg j) ∧ (getD0 cfg.bits j).testBit k = true := by
  intro f
  induction f with
  | zero =>
    intro i
    simp only [patAux, Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro j h1 h2
    omega
  | succ f ih =>
    intro i
    rw [patAux, Nat.testBit_or, Bool.or_eq_true, ih (i + 1)]
    constructor
    · rintro (h | ⟨j, h1, h2, h3, h4⟩)
      · split_ifs at h with hw
        · exact ⟨i, le_rfl, by omega, hw, h⟩
        · simp at h
      · exact ⟨j, by omega, by omega, h3, h4⟩
    · rintro ⟨j, h1, h2, h3, h4⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · left
        rw [ite_eq_left h3]
        exact h4
      · right
        exact ⟨j, hlt, by omega, h3, h4⟩

theorem patAux_lt {nt : ℕ} (hb : ∀ j, getD0 cfg.bits j < 2 ^ nt) (w : ℕ → ℕ) :
    ∀ f i, patAux cfg w i f < 2 ^ nt := by
  intro f
  induction f with
  | zero => intro i; exact Nat.two_pow_pos nt
  | succ f ih =>
    intro i
    rw [patAux]
    refine Nat.or_lt_two_pow ?_ (ih (i + 1))
    split_ifs
    · exact hb i
    · exact Nat.two_pow_pos nt

end

/-- Setting of the enumeration of `comparisonCost`: the configuration uses `patternConsts`. -/
structure PatHyp (cfg : EnumCfg) (adns : Array ℕ) : Prop where
  bits : cfg.bits = (patternConsts cfg.aps adns).1
  cup : cfg.cup = (patternConsts cfg.aps adns).2.1
  clo : cfg.clo = (patternConsts cfg.aps adns).2.2

section
variable {cfg : EnumCfg} {adns : Array ℕ}

theorem getD0_cfg_bits (hP : PatHyp cfg adns) (j : ℕ) :
    getD0 cfg.bits j =
      if j < cfg.aps.size then (if adns[j]! = 0 then 0 else 2 ^ kf adns j) else 0 := by
  rw [hP.bits, getD0_bits]

theorem bits_lt (hP : PatHyp cfg adns) (j : ℕ) : getD0 cfg.bits j < 2 ^ kf adns cfg.aps.size := by
  rw [getD0_cfg_bits hP]
  split_ifs with h1 h2
  · exact Nat.two_pow_pos _
  · exact Nat.pow_lt_pow_right (by norm_num) (kf_lt adns h1 h2)
  · exact Nat.two_pow_pos _

theorem patOf_lt (hP : PatHyp cfg adns) (w : ℕ → ℕ) :
    patOf cfg 0 w < 2 ^ kf adns cfg.aps.size :=
  patAux_lt (bits_lt hP) w _ _

/-- For a tilted A-prime `q_j`, the pattern has the bit of `j` iff `w q_j ≥ 1`. -/
theorem and_bits_ne_zero_iff (hP : PatHyp cfg adns) (w : ℕ → ℕ) {j : ℕ}
    (hj : j < cfg.aps.size) (hd : adns[j]! ≠ 0) :
    (patOf cfg 0 w &&& getD0 cfg.bits j) ≠ 0 ↔ 1 ≤ w (qf cfg j) := by
  rw [getD0_cfg_bits hP, ite_eq_left hj, ite_eq_right hd, and_two_pow_eq]
  have key : (patOf cfg 0 w).testBit (kf adns j) = true ↔ 1 ≤ w (qf cfg j) := by
    unfold patOf
    rw [testBit_patAux]
    constructor
    · rintro ⟨j', -, hj', hw, hb⟩
      rw [getD0_cfg_bits hP] at hb
      split_ifs at hb with h1 h2
      · simp at hb
      · rw [Nat.testBit_two_pow] at hb
        have := kf_inj adns h2 hd (by simpa using hb)
        subst this
        exact hw
      · simp at hb
    · intro hw
      refine ⟨j, Nat.zero_le _, by omega, hw, ?_⟩
      rw [getD0_cfg_bits hP, ite_eq_left hj, ite_eq_right hd]
      exact Nat.testBit_two_pow_self
  split_ifs with hb
  · exact ⟨fun _ => key.1 hb, fun _ => (Nat.two_pow_pos _).ne'⟩
  · exact ⟨fun h => absurd rfl h, fun hw => absurd (key.2 hw) hb⟩

end

/-! ### `numDen` and `mkC` -/

/-- Numerator factor of `C[pat]` at the A-prime of index `j`. -/
def nfac (aps adns bits : Array ℕ) (pat j : ℕ) : ℕ :=
  if adns[j]! = 0 then aps[j]! - 1
  else if (pat &&& bits[j]! != 0) = true then DDEN * (aps[j]! - 1)
  else aps[j]! * (DDEN - adns[j]!) - DDEN

/-- Denominator factor of `C[pat]` at the A-prime of index `j`. -/
def dfac (aps adns : Array ℕ) (j : ℕ) : ℕ :=
  if adns[j]! = 0 then aps[j]! else aps[j]! * (DDEN - adns[j]!)

theorem numDen_spec (aps adns bits : Array ℕ) (pat : ℕ) : ∀ f i num den,
    patternConsts.numDen aps adns bits pat i num den f =
      (num * ∏ j ∈ Ico i (i + f), nfac aps adns bits pat j,
        den * ∏ j ∈ Ico i (i + f), dfac aps adns j) := by
  intro f
  induction f with
  | zero => intro i num den; simp [patternConsts.numDen]
  | succ f ih =>
    intro i num den
    rw [patternConsts.numDen,
      prod_eq_prod_Ico_succ_bot (show i < i + (f + 1) by omega) (nfac aps adns bits pat),
      prod_eq_prod_Ico_succ_bot (show i < i + (f + 1) by omega) (dfac aps adns),
      show i + (f + 1) = i + 1 + f by omega]
    by_cases h0 : adns[i]! = 0
    · have hc : (adns[i]! == 0) = true := by simp [h0]
      have hn : nfac aps adns bits pat i = aps[i]! - 1 := by unfold nfac; rw [ite_eq_left h0]
      have hd : dfac aps adns i = aps[i]! := by unfold dfac; rw [ite_eq_left h0]
      rw [ite_eq_left hc, ih, hn, hd]
      refine Prod.ext ?_ ?_ <;> simp only <;> ring
    · have hc : ¬ (adns[i]! == 0) = true := by simp [h0]
      have hd : dfac aps adns i = aps[i]! * (DDEN - adns[i]!) := by
        unfold dfac; rw [ite_eq_right h0]
      rw [ite_eq_right hc, hd]
      simp only
      by_cases hb : (pat &&& bits[i]! != 0) = true
      · have hn : nfac aps adns bits pat i = DDEN * (aps[i]! - 1) := by
          unfold nfac; rw [ite_eq_right h0, ite_eq_left hb]
        rw [ite_eq_left hb, ih, hn]
        refine Prod.ext ?_ ?_ <;> simp only <;> ring
      · have hn : nfac aps adns bits pat i = aps[i]! * (DDEN - adns[i]!) - DDEN := by
          unfold nfac; rw [ite_eq_right h0, ite_eq_right hb]
        rw [ite_eq_right hb, ih, hn]
        refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem mkC_spec (aps adns bits : Array ℕ) : ∀ f pat (cup clo : Array ℕ), cup.size = pat →
    clo.size = pat → ∀ k, k < pat + f →
      getD0 (patternConsts.mkC aps adns bits pat cup clo f).1 k =
        (if k < pat then getD0 cup k else
          ratUp (patternConsts.numDen aps adns bits k 0 1 1 aps.size).1
            (patternConsts.numDen aps adns bits k 0 1 1 aps.size).2) ∧
      getD0 (patternConsts.mkC aps adns bits pat cup clo f).2 k =
        (if k < pat then getD0 clo k else
          ratDn (patternConsts.numDen aps adns bits k 0 1 1 aps.size).1
            (patternConsts.numDen aps adns bits k 0 1 1 aps.size).2) := by
  intro f
  induction f with
  | zero =>
    intro pat cup clo _ _ k hk
    simp only [patternConsts.mkC]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    exact ⟨rfl, rfl⟩
  | succ f ih =>
    intro pat cup clo hc hl k hk
    rw [patternConsts.mkC]
    generalize hnd : patternConsts.numDen aps adns bits pat 0 1 1 aps.size = nd
    obtain ⟨num, den⟩ := nd
    simp only
    obtain ⟨h1, h2⟩ := ih (pat + 1) (cup.push (ratUp num den)) (clo.push (ratDn num den))
      (by rw [Array.size_push, hc]) (by rw [Array.size_push, hl]) k (by omega)
    rw [h1, h2, getD0_push, getD0_push, hc, hl]
    refine ⟨?_, ?_⟩
    · by_cases hk1 : k < pat
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left hk1]
      · by_cases hk2 : k = pat
        · subst hk2
          rw [ite_eq_left (by omega), ite_eq_left rfl, ite_eq_right hk1, hnd]
        · rw [ite_eq_right (by omega), ite_eq_right hk1]
    · by_cases hk1 : k < pat
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left hk1]
      · by_cases hk2 : k = pat
        · subst hk2
          rw [ite_eq_left (by omega), ite_eq_left rfl, ite_eq_right hk1, hnd]
        · rw [ite_eq_right (by omega), ite_eq_right hk1]

theorem getD0_cup_clo (aps adns : Array ℕ) {pat : ℕ}
    (hpat : pat < 2 ^ kf adns aps.size) :
    getD0 (patternConsts aps adns).2.1 pat =
        ratUp (∏ j ∈ range aps.size, nfac aps adns (patternConsts aps adns).1 pat j)
          (∏ j ∈ range aps.size, dfac aps adns j) ∧
    getD0 (patternConsts aps adns).2.2 pat =
        ratDn (∏ j ∈ range aps.size, nfac aps adns (patternConsts aps adns).1 pat j)
          (∏ j ∈ range aps.size, dfac aps adns j) := by
  have hb := patternConsts_bits aps adns
  have hnt := mkBits_nt aps adns
  unfold patternConsts at hb ⊢
  generalize hm : patternConsts.mkBits adns 0 0 #[] aps.size = m at hb hnt ⊢
  obtain ⟨bits, nt⟩ := m
  simp only at hb hnt ⊢
  subst hnt
  obtain ⟨h1, h2⟩ := mkC_spec aps adns bits (1 <<< kf adns aps.size) 0 #[] #[] rfl rfl pat
    (by rw [Nat.one_shiftLeft]; omega)
  rw [h1, h2, ite_eq_right (by omega), ite_eq_right (by omega), numDen_spec, range_eq_Ico,
    Nat.one_mul, Nat.one_mul, Nat.zero_add]
  exact ⟨rfl, rfl⟩

/-! ### Rounding primitives in `ℝ` -/

theorem cast_ONE : ((ONE : ℕ) : ℝ) = 2 ^ 62 := by
  rw [ONE_eq]; push_cast; ring

theorem cast_DDEN : ((DDEN : ℕ) : ℝ) = 10 ^ 9 := by
  rw [show DDEN = 10 ^ 9 from rfl]; push_cast; ring

theorem cdiv_ge {a b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  have h1 : (a : ℝ) ≤ (cdiv a b : ℝ) * b := by exact_mod_cast cdiv_spec (a := a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  exact h1

theorem cast_div_le (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := Nat.cast_div_le

theorem cast_sub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

theorem pv_ratUp_ge {num den : ℕ} (h : 0 < den) : (num : ℝ) / den ≤ pv (ratUp num den) := by
  have h1 : (num : ℝ) * ONE ≤ (ratUp num den : ℝ) * den := by
    exact_mod_cast ratUp_spec (num := num) h
  rw [cast_ONE] at h1
  have hd : (0 : ℝ) < den := by exact_mod_cast h
  unfold pv
  rw [div_le_div_iff₀ hd (by positivity)]
  exact h1

theorem pv_ratDn_le {num den : ℕ} (h : 0 < den) : pv (ratDn num den) ≤ (num : ℝ) / den := by
  have h1 : (ratDn num den : ℝ) * den ≤ (num : ℝ) * ONE := by
    exact_mod_cast ratDn_spec num den
  rw [cast_ONE] at h1
  have hd : (0 : ℝ) < den := by exact_mod_cast h
  unfold pv
  rw [div_le_div_iff₀ (by positivity) hd]
  exact h1

/-! ### The leaf probability -/

section
variable {cfg : EnumCfg} {adns : Array ℕ}

theorem qf_eq_getElem! (cfg : EnumCfg) (j : ℕ) : qf cfg j = cfg.aps[j]! := getD0_eq_getElem! _ _

theorem two_le_qf (h : EnumHyp cfg) {j : ℕ} (hj : j < cfg.aps.size) : 2 ≤ qf cfg j :=
  (h.prime j hj).two_le

theorem dfac_pos (h : EnumHyp cfg) (hd : ∀ j < cfg.aps.size, 2 * adns[j]! ≤ DDEN) {j : ℕ}
    (hj : j < cfg.aps.size) : 0 < dfac cfg.aps adns j := by
  have hq := two_le_qf h hj
  rw [qf_eq_getElem!] at hq
  have := hd j hj
  unfold dfac
  split_ifs
  · omega
  · exact Nat.mul_pos (by omega) (by unfold DDEN at *; omega)

/-- One factor of `C[pat]`: `F(q_j) = nfac/dfac` for the pattern of the configuration. -/
theorem factor_eq (h : EnumHyp cfg) (hP : PatHyp cfg adns) (ν : ℕ → ℝ)
    (hν : ∀ j < cfg.aps.size, ν (qf cfg j) = (DDEN : ℝ) / ((DDEN : ℝ) - (adns[j]! : ℝ)))
    (hd : ∀ j < cfg.aps.size, 2 * adns[j]! ≤ DDEN) (w : ℕ → ℕ) {j : ℕ}
    (hj : j < cfg.aps.size) :
    (if w (qf cfg j) = 0 then 1 - ν (qf cfg j) / (qf cfg j : ℝ)
      else ν (qf cfg j) * (1 - ((qf cfg j : ℕ) : ℝ)⁻¹)) =
      (nfac cfg.aps adns cfg.bits (patOf cfg 0 w) j : ℝ) / (dfac cfg.aps adns j : ℝ) := by
  have hq2 := two_le_qf h hj
  have hdj := hd j hj
  have hνj := hν j hj
  have hq : (2 : ℝ) ≤ (qf cfg j : ℝ) := by exact_mod_cast hq2
  have hq0 : (qf cfg j : ℝ) ≠ 0 := by positivity
  have hD : (DDEN : ℝ) = 10 ^ 9 := cast_DDEN
  have hdle : (2 : ℝ) * (adns[j]! : ℝ) ≤ DDEN := by exact_mod_cast hdj
  unfold nfac dfac
  rw [← qf_eq_getElem! cfg j]
  by_cases h0 : adns[j]! = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    rw [h0, Nat.cast_zero, sub_zero, div_self (by rw [hD]; norm_num)] at hνj
    rw [hνj, Nat.cast_sub (by omega : 1 ≤ qf cfg j)]
    split_ifs <;> field_simp <;> ring
  · rw [ite_eq_right h0, ite_eq_right h0]
    have hbits : (patOf cfg 0 w &&& cfg.bits[j]! != 0) = true ↔ 1 ≤ w (qf cfg j) := by
      rw [← and_bits_ne_zero_iff hP w hj h0, getD0_eq_getElem!]
      simp
    have hnd : (0 : ℝ) < (DDEN : ℝ) - adns[j]! := by rw [hD] at hdle ⊢; linarith
    have hnd' : adns[j]! ≤ DDEN := by unfold DDEN at *; omega
    have hqnd : DDEN ≤ qf cfg j * (DDEN - adns[j]!) := by
      have : DDEN ≤ 2 * (DDEN - adns[j]!) := by unfold DDEN at *; omega
      exact this.trans (Nat.mul_le_mul_right _ hq2)
    rw [hνj]
    by_cases hw : w (qf cfg j) = 0
    · have hb : ¬ (patOf cfg 0 w &&& cfg.bits[j]! != 0) = true := by
        rw [hbits]; omega
      rw [ite_eq_left hw, ite_eq_right hb, Nat.cast_sub hqnd, Nat.cast_mul, Nat.cast_sub hnd']
      field_simp
    · have hb : (patOf cfg 0 w &&& cfg.bits[j]! != 0) = true := by
        rw [hbits]; omega
      rw [ite_eq_right hw, ite_eq_left hb, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hnd',
        Nat.cast_sub (by omega : 1 ≤ qf cfg j)]
      field_simp
      ring

/-- **`π(w) · s(w) = C[pat]`** below the caps, with `C[pat] = Π nfac / Π dfac`. -/
theorem weight_mul_smooth (h : EnumHyp cfg) (hP : PatHyp cfg adns) (ν : ℕ → ℝ)
    (hν : ∀ j < cfg.aps.size, ν (qf cfg j) = (DDEN : ℝ) / ((DDEN : ℝ) - (adns[j]! : ℝ)))
    (hd : ∀ j < cfg.aps.size, 2 * adns[j]! ≤ DDEN) {γ : ℕ → ℕ} {w : ℕ → ℕ}
    (hw : ∀ q ∈ Ps cfg 0, w q < γ q) :
    weight (Ps cfg 0) ν γ w * smooth (Ps cfg 0) w =
      (∏ j ∈ range cfg.aps.size, (nfac cfg.aps adns cfg.bits (patOf cfg 0 w) j : ℝ)) /
        (∏ j ∈ range cfg.aps.size, (dfac cfg.aps adns j : ℝ)) := by
  have hs : (smooth (Ps cfg 0) w : ℝ) ≠ 0 := by
    have := smooth_pos (pos_of_mem_Ps h (i := 0)) w
    positivity
  rw [CheckerMath.weight_eq_div_smooth hw, div_mul_cancel₀ _ hs, ← prod_div_distrib]
  have hinj : Set.InjOn (qf cfg) (Ico 0 cfg.aps.size : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_Ico, Set.mem_Ico] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact qf_ne h hlt hb.2 hab.symm
    · exact qf_ne h hlt ha.2 hab
  unfold Ps
  rw [prod_image hinj, range_eq_Ico]
  refine prod_congr rfl fun j hj => ?_
  exact factor_eq h hP ν hν hd w (mem_Ico.1 hj).2

/-- **Leaf probability bounds**: `⌊clo[pat]/s⌋/2^62 ≤ π(w) ≤ ⌈cup[pat]/s⌉/2^62`. -/
theorem leaf_prob_bounds (h : EnumHyp cfg) (hP : PatHyp cfg adns) (ν : ℕ → ℝ)
    (hν : ∀ j < cfg.aps.size, ν (qf cfg j) = (DDEN : ℝ) / ((DDEN : ℝ) - (adns[j]! : ℝ)))
    (hd : ∀ j < cfg.aps.size, 2 * adns[j]! ≤ DDEN) {γ : ℕ → ℕ} {w : ℕ → ℕ}
    (hw : ∀ q ∈ Ps cfg 0, w q < γ q) :
    pv (getD0 cfg.clo (patOf cfg 0 w) / smooth (Ps cfg 0) w) ≤ weight (Ps cfg 0) ν γ w ∧
      weight (Ps cfg 0) ν γ w ≤ pv (cdiv (getD0 cfg.cup (patOf cfg 0 w)) (smooth (Ps cfg 0) w)) := by
  have hs0 : 0 < smooth (Ps cfg 0) w := smooth_pos (pos_of_mem_Ps h (i := 0)) w
  have hs : (0 : ℝ) < smooth (Ps cfg 0) w := by exact_mod_cast hs0
  have hD : 0 < ∏ j ∈ range cfg.aps.size, dfac cfg.aps adns j :=
    prod_pos fun j hj => dfac_pos h hd (mem_range.1 hj)
  obtain ⟨hcup, hclo⟩ := getD0_cup_clo cfg.aps adns (patOf_lt hP w)
  rw [← hP.bits, ← hP.cup] at hcup
  rw [← hP.bits, ← hP.clo] at hclo
  have hW : weight (Ps cfg 0) ν γ w =
      ((∏ j ∈ range cfg.aps.size, (nfac cfg.aps adns cfg.bits (patOf cfg 0 w) j : ℝ)) /
        (∏ j ∈ range cfg.aps.size, (dfac cfg.aps adns j : ℝ))) / smooth (Ps cfg 0) w := by
    rw [← weight_mul_smooth h hP ν hν hd hw, mul_div_cancel_right₀ _ hs.ne']
  have hcast : ((∏ j ∈ range cfg.aps.size, nfac cfg.aps adns cfg.bits (patOf cfg 0 w) j : ℕ) : ℝ) /
      ((∏ j ∈ range cfg.aps.size, dfac cfg.aps adns j : ℕ) : ℝ) =
      (∏ j ∈ range cfg.aps.size, (nfac cfg.aps adns cfg.bits (patOf cfg 0 w) j : ℝ)) /
        (∏ j ∈ range cfg.aps.size, (dfac cfg.aps adns j : ℝ)) := by
    push_cast; rfl
  rw [hW]
  constructor
  · rw [hclo]
    calc pv (ratDn _ _ / smooth (Ps cfg 0) w)
        ≤ pv (ratDn (∏ j ∈ range cfg.aps.size, nfac cfg.aps adns cfg.bits (patOf cfg 0 w) j)
            (∏ j ∈ range cfg.aps.size, dfac cfg.aps adns j)) / smooth (Ps cfg 0) w := by
          unfold pv
          rw [div_div, mul_comm, ← div_div]
          exact div_le_div_of_nonneg_right (cast_div_le _ _) (by positivity)
      _ ≤ _ := by
          rw [← hcast]
          exact div_le_div_of_nonneg_right (pv_ratDn_le hD) hs.le
  · rw [hcup]
    calc _ ≤ pv (ratUp (∏ j ∈ range cfg.aps.size, nfac cfg.aps adns cfg.bits (patOf cfg 0 w) j)
            (∏ j ∈ range cfg.aps.size, dfac cfg.aps adns j)) / smooth (Ps cfg 0) w := by
          rw [← hcast]
          exact div_le_div_of_nonneg_right (pv_ratUp_ge hD) hs.le
      _ ≤ pv (cdiv (ratUp _ _) (smooth (Ps cfg 0) w)) := by
          unfold pv
          rw [div_div, mul_comm, ← div_div]
          exact div_le_div_of_nonneg_right (cdiv_ge hs0) (by positivity)

end

end MinModulus.CheckerSound.C
