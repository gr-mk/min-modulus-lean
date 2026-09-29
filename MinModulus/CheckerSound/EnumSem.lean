import MinModulus.CheckerSound.EnumBasic

/-!
# `CheckerSound.EnumSem` (agent CS-C): semantics of the depth-first enumeration `runEnum`

Status: complete, no `sorry`.

Setting: an enumeration configuration `cfg : EnumCfg` whose A-primes `q_j = aps[j]` (`qf cfg j`)
are primes in strictly increasing order and `M2 ≤ M1` (`EnumHyp`). `Ps cfg i` is the set of the
A-primes with index `≥ i`; `L cfg γ i s` is the set of exponent vectors `w` of these primes (caps
`γ`) with `s · s(w) ≤ X` (the leaves below the node `(i, s)`).

**Main result** (`runEnum_view`): if the run ends with `ok = true` and the caps `γ` admit every
exponent that fits below `X` (`CapOK`), then the five accumulator arrays are exactly the sums
over the enumerated configurations `w ∈ L cfg γ 0 1 = {w ∈ box A γ : s(w) ≤ X}` of the leaf
contributions: `view (runEnum cfg _) = Σ_{w} LV cfg (s(w)) (patOf cfg 0 w)`, where
`LV cfg s pat = leafView cfg s τ(s) pat σ₁(s) σ₂(s)` with the **true** values `τ(s) = #divisors`,
`σ_j(s) = #{d ∣ s : d < M_j}`. Hence every configuration is visited exactly once, with the
correct `s`, `τ(s)`, `σ₁`, `σ₂`, and the pattern `patOf cfg 0 w` (the `OR` of `bits[j]` over the
`j` with `w q_j ≥ 1`).

Proof structure (mutual induction on the fuel of `enumNode`/`enumExp`):
* `enum_frame` (unconditional): the children only write the buffer at positions `≥ len`;
* `enum_ok`: `ok` only goes from `true` to `false`;
* `enum_view`: the node invariant `NodeInv` (`buf[0..len)` = the small divisors `< M1` of `s`,
  `sig2 = #{d ∣ s : d < M2}`, `τ = τ(s)`, `s` coprime to the remaining primes) and the exponent
  invariant `ExpInv` (`buf[bs..be)` = the small divisors with exact `q`-exponent `a - 1`) give the
  `view` equations; the recursion over the primes is `sum_L_succ` (the unweighted analogue of
  `CheckerMath.enumSum_insert`), the pruning is `L_of_gt` (primes increasing), the exponent
  loop stops at `L_of_lt`.
-/

namespace MinModulus.CheckerSound.C

open MinModulus.CheckerImpl MinModulus.Smooth Finset

/-! ### The A-primes and the enumerated configurations -/

/-- The `j`-th A-prime of the enumeration. -/
def qf (cfg : EnumCfg) (j : ℕ) : ℕ := getD0 cfg.aps j

/-- The A-primes with index in `[i, n)`, `n = aps.size`. -/
def Ps (cfg : EnumCfg) (i : ℕ) : Finset ℕ := (Ico i cfg.aps.size).image (qf cfg)

/-- Standing hypotheses on the enumeration configuration. -/
structure EnumHyp (cfg : EnumCfg) : Prop where
  prime : ∀ j < cfg.aps.size, (qf cfg j).Prime
  lt : ∀ j j', j < j' → j' < cfg.aps.size → qf cfg j < qf cfg j'
  M21 : cfg.M2 ≤ cfg.M1

/-- The caps admit every exponent that fits below `X`. -/
def CapOK (cfg : EnumCfg) (γ : ℕ → ℕ) : Prop :=
  ∀ j < cfg.aps.size, ∀ b, qf cfg j ^ b ≤ cfg.X → b ≤ γ (qf cfg j)

/-- The enumerated configurations below the node `(i, s)`: exponent vectors `w` of the A-primes
with index `≥ i` (caps `γ`) with `s · s(w) ≤ X`. -/
def L (cfg : EnumCfg) (γ : ℕ → ℕ) (i s : ℕ) : Finset (ℕ → ℕ) :=
  (box (Ps cfg i) γ).filter (fun w => s * smooth (Ps cfg i) w ≤ cfg.X)

section
variable {cfg : EnumCfg}

theorem mem_Ps {i q : ℕ} : q ∈ Ps cfg i ↔ ∃ j, (i ≤ j ∧ j < cfg.aps.size) ∧ qf cfg j = q := by
  simp only [Ps, mem_image, mem_Ico]

theorem Ps_of_le {i : ℕ} (hi : cfg.aps.size ≤ i) : Ps cfg i = ∅ := by
  simp [Ps, Ico_eq_empty_of_le hi]

theorem Ps_succ {i : ℕ} (hi : i < cfg.aps.size) :
    Ps cfg i = insert (qf cfg i) (Ps cfg (i + 1)) := by
  ext q
  simp only [mem_insert, mem_Ps]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · left; rfl
    · right; exact ⟨j, ⟨h, h2⟩, rfl⟩
  · rintro (rfl | ⟨j, ⟨h1, h2⟩, rfl⟩)
    · exact ⟨i, ⟨le_rfl, hi⟩, rfl⟩
    · exact ⟨j, ⟨by omega, h2⟩, rfl⟩

theorem qf_notMem_Ps (h : EnumHyp cfg) (i : ℕ) : qf cfg i ∉ Ps cfg (i + 1) := by
  rw [mem_Ps]
  rintro ⟨j, ⟨hj, hjn⟩, hq⟩
  have := h.lt i j (by omega) hjn
  omega

theorem prime_of_mem_Ps (h : EnumHyp cfg) {i q : ℕ} (hq : q ∈ Ps cfg i) : q.Prime := by
  obtain ⟨j, ⟨-, hj⟩, rfl⟩ := mem_Ps.1 hq
  exact h.prime j hj

theorem pos_of_mem_Ps (h : EnumHyp cfg) {i : ℕ} : ∀ q ∈ Ps cfg i, 0 < q :=
  fun _ hq => (prime_of_mem_Ps h hq).pos

theorem qf_le_of_mem_Ps (h : EnumHyp cfg) {i q : ℕ} (hq : q ∈ Ps cfg i) : qf cfg i ≤ q := by
  obtain ⟨j, ⟨hij, hj⟩, rfl⟩ := mem_Ps.1 hq
  rcases Nat.eq_or_lt_of_le hij with rfl | h'
  · exact le_rfl
  · exact (h.lt i j h' hj).le

theorem qf_ne (h : EnumHyp cfg) {i j : ℕ} (hij : i < j) (hj : j < cfg.aps.size) :
    qf cfg j ≠ qf cfg i := by
  have := h.lt i j hij hj
  omega

/-- **One prime at a time** (unweighted `enumSum_insert`): for `i < n`,
`Σ_{w ∈ L(i, s)} F w = Σ_{a ≤ γ q_i} Σ_{w ∈ L(i+1, s q_i^a)} F (update w q_i a)`. -/
theorem sum_L_succ {M : Type*} [AddCommMonoid M] (h : EnumHyp cfg) {i : ℕ}
    (hi : i < cfg.aps.size) (γ : ℕ → ℕ) (s : ℕ) (F : (ℕ → ℕ) → M) :
    ∑ w ∈ L cfg γ i s, F w = ∑ a ∈ range (γ (qf cfg i) + 1),
      ∑ w ∈ L cfg γ (i + 1) (s * qf cfg i ^ a), F (Function.update w (qf cfg i) a) := by
  have hq := qf_notMem_Ps h i
  unfold L
  rw [sum_filter, Ps_succ hi, sum_box_insert hq]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun w _ => ?_
  rw [smooth_insert hq, Function.update_self, smooth_update_of_notMem hq, mul_assoc]

@[simp] theorem smooth_zero (S : Finset ℕ) : smooth S 0 = 1 := by
  simp [smooth]

/-- No A-prime left: the only leaf is `w = 0`. -/
theorem L_of_le {i : ℕ} (hi : cfg.aps.size ≤ i) (γ : ℕ → ℕ) {s : ℕ} (hs : s ≤ cfg.X) :
    L cfg γ i s = {0} := by
  unfold L
  rw [Ps_of_le hi, box_empty, filter_singleton, smooth_zero, Nat.mul_one, ite_eq_left hs]

/-- **Pruning**: if `s · q_i > X` then (primes increasing) `w = 0` is the only leaf. -/
theorem L_of_gt (h : EnumHyp cfg) {i : ℕ} (γ : ℕ → ℕ) {s : ℕ} (hs : s ≤ cfg.X)
    (hsq : cfg.X < s * qf cfg i) : L cfg γ i s = {0} := by
  ext w
  simp only [L, mem_filter, mem_singleton]
  constructor
  · rintro ⟨hw, hwX⟩
    rw [mem_box] at hw
    funext r
    by_cases hr : r ∈ Ps cfg i
    · by_contra hne
      have hne' : w r ≠ 0 := hne
      have h1 : r ∣ smooth (Ps cfg i) w :=
        (dvd_pow_self r hne').trans (dvd_prod_of_mem (fun q => q ^ w q) hr)
      have h2 : qf cfg i ≤ smooth (Ps cfg i) w :=
        (qf_le_of_mem_Ps h hr).trans
          (Nat.le_of_dvd (smooth_pos (pos_of_mem_Ps h) w) h1)
      have : s * qf cfg i ≤ s * smooth (Ps cfg i) w := Nat.mul_le_mul_left s h2
      omega
    · exact hw.2 r hr
  · rintro rfl
    refine ⟨zero_mem_box _ _, ?_⟩
    rw [smooth_zero, Nat.mul_one]
    exact hs

/-- A node above `X` has no leaf. -/
theorem L_of_lt (h : EnumHyp cfg) {i : ℕ} (γ : ℕ → ℕ) {s : ℕ} (hs : cfg.X < s) :
    L cfg γ i s = ∅ := by
  unfold L
  rw [filter_eq_empty_iff]
  intro w _ hw
  have h1 : 1 ≤ smooth (Ps cfg i) w := smooth_pos (pos_of_mem_Ps h) w
  have : s ≤ s * smooth (Ps cfg i) w := Nat.le_mul_of_pos_right s h1
  omega

end

/-! ### The pattern of a configuration -/

/-- `OR` of `bits[j]` over the indices `j ∈ [i, i + f)` with `w q_j ≥ 1`. -/
def patAux (cfg : EnumCfg) (w : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, f + 1 => (if 1 ≤ w (qf cfg i) then getD0 cfg.bits i else 0) ||| patAux cfg w (i + 1) f

/-- The pattern contributed by the A-primes with index `≥ i`. -/
def patOf (cfg : EnumCfg) (i : ℕ) (w : ℕ → ℕ) : ℕ := patAux cfg w i (cfg.aps.size - i)

section
variable {cfg : EnumCfg}

theorem patOf_succ {i : ℕ} (hi : i < cfg.aps.size) (w : ℕ → ℕ) :
    patOf cfg i w =
      (if 1 ≤ w (qf cfg i) then getD0 cfg.bits i else 0) ||| patOf cfg (i + 1) w := by
  unfold patOf
  obtain ⟨k, hk⟩ : ∃ k, cfg.aps.size - i = k + 1 := ⟨cfg.aps.size - i - 1, by omega⟩
  rw [hk, patAux, show cfg.aps.size - (i + 1) = k by omega]

theorem patOf_of_le {i : ℕ} (hi : cfg.aps.size ≤ i) (w : ℕ → ℕ) : patOf cfg i w = 0 := by
  unfold patOf
  rw [Nat.sub_eq_zero_of_le hi, patAux]

theorem patAux_congr {w w' : ℕ → ℕ} :
    ∀ f i, (∀ j, i ≤ j → j < i + f → w (qf cfg j) = w' (qf cfg j)) →
      patAux cfg w i f = patAux cfg w' i f := by
  intro f
  induction f with
  | zero => intro i _; rfl
  | succ f ih =>
    intro i hw
    rw [patAux, patAux, hw i le_rfl (by omega),
      ih (i + 1) fun j h1 h2 => hw j (by omega) (by omega)]

theorem patOf_update (h : EnumHyp cfg) (i : ℕ) (w : ℕ → ℕ) (a : ℕ) :
    patOf cfg (i + 1) (Function.update w (qf cfg i) a) = patOf cfg (i + 1) w := by
  unfold patOf
  refine patAux_congr _ _ fun j h1 h2 => ?_
  rw [Function.update_of_ne (qf_ne h (by omega) (by omega))]

theorem patAux_zero : ∀ f i, patAux cfg 0 i f = 0 := by
  intro f
  induction f with
  | zero => intro i; rfl
  | succ f ih =>
    intro i
    rw [patAux, ih]
    simp

theorem patOf_zero (i : ℕ) : patOf cfg i 0 = 0 := patAux_zero _ _

end

/-! ### Leaf data -/

/-- What the enumeration adds at the leaf with value `s` and pattern `pat`, with the true
`τ(s)`, `σ₁(s) = #{d ∣ s : d < M1}`, `σ₂(s) = #{d ∣ s : d < M2}`. -/
def LV (cfg : EnumCfg) (s pat : ℕ) : Fin 5 → ℕ → ℕ :=
  leafView cfg s s.divisors.card pat (s.divisors.filter (· < cfg.M1)).card
    (s.divisors.filter (· < cfg.M2)).card

/-- Invariant at a node `(i, s)`. -/
def NodeInv (cfg : EnumCfg) (i s τ len sig2 : ℕ) (buf : Array ℕ) : Prop :=
  0 < s ∧ s ≤ cfg.X ∧ (∀ j, i ≤ j → j < cfg.aps.size → Nat.Coprime (qf cfg j) s) ∧
  τ = s.divisors.card ∧ seg buf 0 len = (s.divisors.filter (· < cfg.M1)).val ∧
  sig2 = (s.divisors.filter (· < cfg.M2)).card

/-- Invariant at the exponent `a ≥ 1` of `q_i` below the node `(i, s)`. -/
def ExpInv (cfg : EnumCfg) (i s a bs be len sig2 : ℕ) (buf : Array ℕ) : Prop :=
  i < cfg.aps.size ∧ 0 < s ∧ (∀ j, i ≤ j → j < cfg.aps.size → Nat.Coprime (qf cfg j) s) ∧
  1 ≤ a ∧ s * qf cfg i ^ a ≤ cfg.X ∧ be = len ∧ bs ≤ be ∧
  seg buf 0 len = ((s * qf cfg i ^ (a - 1)).divisors.filter (· < cfg.M1)).val ∧
  seg buf bs be = (s.divisors.val.map (· * qf cfg i ^ (a - 1))).filter (· < cfg.M1) ∧
  sig2 = ((s * qf cfg i ^ (a - 1)).divisors.filter (· < cfg.M2)).card

/-! ### Frame and `ok` monotonicity (no invariant needed) -/

theorem extendBlock_frame (cfg : EnumCfg) (q be : ℕ) :
    ∀ (fuel i len sig2 : ℕ) (acc : EnumAcc),
    (extendBlock cfg q be i len sig2 acc fuel).1.buf.size = acc.buf.size ∧
    (∀ j < len, getD0 (extendBlock cfg q be i len sig2 acc fuel).1.buf j = getD0 acc.buf j) ∧
    len ≤ (extendBlock cfg q be i len sig2 acc fuel).2.1 ∧
    ((extendBlock cfg q be i len sig2 acc fuel).1.ok = true → acc.ok = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i len sig2 acc
    rw [extendBlock]
    split_ifs <;> simp
  | succ f ih =>
    intro i len sig2 acc
    rw [extendBlock]
    simp only
    generalize (if getD0 acc.buf i * q < cfg.M2 then sig2 + 1 else sig2) = S
    split_ifs with hib hv hlen
    · obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (len + 1) S
        { acc with buf := acc.buf.set! len (getD0 acc.buf i * q) }
      refine ⟨h1.trans (size_set! _ _ _), fun j hj => (h2 j (by omega)).trans ?_, by omega, h4⟩
      simp only
      rw [getD0_set!, ite_eq_right (by omega)]
    · simp
    · exact ih (i + 1) len sig2 acc
    · simp

theorem enum_frame (cfg : EnumCfg) : ∀ f : ℕ,
    (∀ i s τ pat len sig2 (acc : EnumAcc),
      (enumNode cfg f i s τ pat len sig2 acc).buf.size = acc.buf.size ∧
      ∀ j < len, getD0 (enumNode cfg f i s τ pat len sig2 acc).buf j = getD0 acc.buf j) ∧
    (∀ i q sa a τ0 pat bs be len sig2 (acc : EnumAcc),
      (enumExp cfg f i q sa a τ0 pat bs be len sig2 acc).buf.size = acc.buf.size ∧
      ∀ j < len, getD0 (enumExp cfg f i q sa a τ0 pat bs be len sig2 acc).buf j =
        getD0 acc.buf j) := by
  intro f
  induction f with
  | zero =>
    refine ⟨fun i s τ pat len sig2 acc => ?_, fun i q sa a τ0 pat bs be len sig2 acc => ?_⟩
    · rw [enumNode]; exact ⟨rfl, fun _ _ => rfl⟩
    · rw [enumExp]; exact ⟨rfl, fun _ _ => rfl⟩
  | succ f ih =>
    obtain ⟨ihN, ihE⟩ := ih
    refine ⟨fun i s τ pat len sig2 acc => ?_, fun i q sa a τ0 pat bs be len sig2 acc => ?_⟩
    · rw [enumNode]
      split_ifs
      · simp only
        obtain ⟨h1, h2⟩ := ihN (i + 1) s τ pat len sig2 acc
        obtain ⟨h3, h4⟩ := ihE i (getD0 cfg.aps i) (s * getD0 cfg.aps i) 1 τ
          (pat ||| getD0 cfg.bits i) 0 len len sig2 (enumNode cfg f (i + 1) s τ pat len sig2 acc)
        exact ⟨h3.trans h1, fun j hj => (h4 j hj).trans (h2 j hj)⟩
      · rw [leaf_buf]; exact ⟨rfl, fun _ _ => rfl⟩
    · rw [enumExp]
      obtain ⟨e1, e2, e3, -⟩ := extendBlock_frame cfg q be (be - bs + 1) bs len sig2 acc
      generalize extendBlock cfg q be bs len sig2 acc (be - bs + 1) = r at e1 e2 e3
      obtain ⟨acc1, len', sig2'⟩ := r
      simp only at e1 e2 e3 ⊢
      obtain ⟨h1, h2⟩ := ihN (i + 1) sa (τ0 * (a + 1)) pat len' sig2' acc1
      split_ifs
      · obtain ⟨h3, h4⟩ := ihE i q (sa * q) (a + 1) τ0 pat len len' len' sig2'
          (enumNode cfg f (i + 1) sa (τ0 * (a + 1)) pat len' sig2' acc1)
        exact ⟨h3.trans (h1.trans e1),
          fun j hj => (h4 j (by omega)).trans ((h2 j (by omega)).trans (e2 j hj))⟩
      · exact ⟨h1.trans e1, fun j hj => (h2 j (by omega)).trans (e2 j hj)⟩

theorem enum_ok (cfg : EnumCfg) : ∀ f : ℕ,
    (∀ i s τ pat len sig2 (acc : EnumAcc),
      (enumNode cfg f i s τ pat len sig2 acc).ok = true → acc.ok = true) ∧
    (∀ i q sa a τ0 pat bs be len sig2 (acc : EnumAcc),
      (enumExp cfg f i q sa a τ0 pat bs be len sig2 acc).ok = true → acc.ok = true) := by
  intro f
  induction f with
  | zero =>
    refine ⟨fun i s τ pat len sig2 acc h => ?_, fun i q sa a τ0 pat bs be len sig2 acc h => ?_⟩
    · rw [enumNode] at h; simp at h
    · rw [enumExp] at h; simp at h
  | succ f ih =>
    obtain ⟨ihN, ihE⟩ := ih
    refine ⟨fun i s τ pat len sig2 acc h => ?_, fun i q sa a τ0 pat bs be len sig2 acc h => ?_⟩
    · rw [enumNode] at h
      split_ifs at h
      · exact ihN _ _ _ _ _ _ _ (ihE _ _ _ _ _ _ _ _ _ _ _ h)
      · exact leaf_ok _ _ _ _ _ _ _ h
    · rw [enumExp] at h
      obtain ⟨-, -, -, e4⟩ := extendBlock_frame cfg q be (be - bs + 1) bs len sig2 acc
      generalize extendBlock cfg q be bs len sig2 acc (be - bs + 1) = r at e4 h
      obtain ⟨acc1, len', sig2'⟩ := r
      simp only at e4 h
      split_ifs at h
      · exact e4 (ihN _ _ _ _ _ _ _ (ihE _ _ _ _ _ _ _ _ _ _ _ h))
      · exact e4 (ihN _ _ _ _ _ _ _ h)

/-! ### The divisor invariants -/

section
variable {cfg : EnumCfg}

/-- Invariant of the child node `(i+1, s q^a)` after `extendBlock`. -/
theorem nodeInv_child (h : EnumHyp cfg) {i s a len len' sig2' : ℕ} {buf' : Array ℕ}
    (hi : i < cfg.aps.size) (hs : 0 < s)
    (hcop : ∀ j, i ≤ j → j < cfg.aps.size → Nat.Coprime (qf cfg j) s) (ha : 1 ≤ a)
    (hX : s * qf cfg i ^ a ≤ cfg.X)
    (hseg0 : seg buf' 0 len = ((s * qf cfg i ^ (a - 1)).divisors.filter (· < cfg.M1)).val)
    (hnew : seg buf' len len' = (s.divisors.val.map (· * qf cfg i ^ a)).filter (· < cfg.M1))
    (hlen : len ≤ len')
    (hsig : sig2' = ((s * qf cfg i ^ (a - 1)).divisors.filter (· < cfg.M2)).card +
      ((s.divisors.val.map (· * qf cfg i ^ a)).filter (· < cfg.M1)).countP (· < cfg.M2)) :
    NodeInv cfg (i + 1) (s * qf cfg i ^ a) (s.divisors.card * (a + 1)) len' sig2' buf' := by
  have hq : (qf cfg i).Prime := h.prime i hi
  have hqs : Nat.Coprime (qf cfg i) s := hcop i le_rfl hi
  have hdiv := divisors_mul_pow_val hs hq hqs ha
  refine ⟨Nat.mul_pos hs (pow_pos hq.pos a), hX, fun j hj hjn => ?_, ?_, ?_, ?_⟩
  · refine Nat.Coprime.mul_right (hcop j (by omega) hjn) (Nat.Coprime.pow_right _ ?_)
    exact (Nat.coprime_primes (h.prime j hjn) hq).2 (qf_ne h (by omega) hjn)
  · rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left a hqs).symm,
      card_divisors_prime_pow hq]
  · rw [seg_split buf' (Nat.zero_le len) hlen, hseg0, hnew, Finset.filter_val, Finset.filter_val,
      hdiv, Multiset.filter_add]
  · rw [hsig, countP_filter_of_le _ h.M21, Finset.card_def, Finset.card_def, Finset.filter_val,
      Finset.filter_val, hdiv, Multiset.filter_add, Multiset.card_add]

end

/-! ### The main induction -/

section
variable {cfg : EnumCfg}

theorem enum_view (h : EnumHyp cfg) {γ : ℕ → ℕ} (hγ : CapOK cfg γ) : ∀ f : ℕ,
    (∀ i s τ pat len sig2 (acc : EnumAcc), NodeInv cfg i s τ len sig2 acc.buf →
      (enumNode cfg f i s τ pat len sig2 acc).ok = true →
      view (enumNode cfg f i s τ pat len sig2 acc) = view acc +
        ∑ w ∈ L cfg γ i s, LV cfg (s * smooth (Ps cfg i) w) (pat ||| patOf cfg i w)) ∧
    (∀ i q sa a τ0 pat bs be len sig2 (acc : EnumAcc) (s : ℕ), q = qf cfg i →
      sa = s * q ^ a → τ0 = s.divisors.card → ExpInv cfg i s a bs be len sig2 acc.buf →
      (enumExp cfg f i q sa a τ0 pat bs be len sig2 acc).ok = true →
      view (enumExp cfg f i q sa a τ0 pat bs be len sig2 acc) = view acc +
        ∑ b ∈ Ico a (γ q + 1), ∑ w ∈ L cfg γ (i + 1) (s * q ^ b),
          LV cfg (s * q ^ b * smooth (Ps cfg (i + 1)) w) (pat ||| patOf cfg (i + 1) w)) := by
  intro f
  induction f with
  | zero =>
    refine ⟨fun i s τ pat len sig2 acc _ hok => ?_,
      fun i q sa a τ0 pat bs be len sig2 acc s _ _ _ _ hok => ?_⟩
    · rw [enumNode] at hok; simp at hok
    · rw [enumExp] at hok; simp at hok
  | succ f ih =>
    obtain ⟨ihN, ihE⟩ := ih
    obtain ⟨frN, frE⟩ := enum_frame cfg f
    obtain ⟨okN, okE⟩ := enum_ok cfg f
    refine ⟨fun i s τ pat len sig2 acc hinv hok => ?_,
      fun i q sa a τ0 pat bs be len sig2 acc s hq hsa hτ0 hinv hok => ?_⟩
    · -- a node
      obtain ⟨hs0, hsX, hcop, hτ, hseg, hsig⟩ := hinv
      rw [enumNode] at hok ⊢
      by_cases hcond : i < cfg.aps.size ∧ s * getD0 cfg.aps i ≤ cfg.X
      · obtain ⟨hi, hsq⟩ := hcond
        have hc : (decide (i < cfg.aps.size) && decide (s * getD0 cfg.aps i ≤ cfg.X)) = true := by
          simp [hi, hsq]
        rw [ite_eq_left hc] at hok ⊢
        simp only [show getD0 cfg.aps i = qf cfg i from rfl] at hok ⊢
        set acc1 := enumNode cfg f (i + 1) s τ pat len sig2 acc with hacc1
        have hok1 : acc1.ok = true := okE _ _ _ _ _ _ _ _ _ _ _ hok
        have hfr1 := (frN (i + 1) s τ pat len sig2 acc).2
        -- the exponent-0 child
        have hv1 := ihN (i + 1) s τ pat len sig2 acc
          ⟨hs0, hsX, fun j hj hjn => hcop j (by omega) hjn, hτ, hseg, hsig⟩ hok1
        -- the exponents `a ≥ 1`
        have hinvE : ExpInv cfg i s 1 0 len len sig2 acc1.buf := by
          refine ⟨hi, hs0, hcop, le_rfl, by simpa [qf] using hsq, rfl, Nat.zero_le _, ?_, ?_, ?_⟩
          · rw [seg_congr (fun j _ hj => hfr1 j hj), hseg]
            simp
          · rw [seg_congr (fun j _ hj => hfr1 j hj), hseg]
            simp
          · simpa using hsig
        have hvE := ihE i (qf cfg i) (s * qf cfg i) 1 τ (pat ||| getD0 cfg.bits i)
          0 len len sig2 acc1 s rfl (by rw [pow_one]) hτ hinvE hok
        rw [hvE, hv1, add_assoc]
        refine congrArg (view acc + ·) ?_
        rw [sum_L_succ h hi γ s, range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
        simp only [pow_zero, Nat.mul_one, Nat.zero_add]
        refine congrArg₂ (· + ·) (sum_congr rfl fun w _ => ?_)
          (sum_congr rfl fun b hb => sum_congr rfl fun w _ => ?_)
        · rw [Ps_succ hi, smooth_insert (qf_notMem_Ps h i), Function.update_self,
            smooth_update_of_notMem (qf_notMem_Ps h i), patOf_succ hi, Function.update_self,
            patOf_update h, pow_zero, Nat.one_mul]
          simp
        · have hb1 : 1 ≤ b := (mem_Ico.1 hb).1
          rw [Ps_succ hi, smooth_insert (qf_notMem_Ps h i), Function.update_self,
            smooth_update_of_notMem (qf_notMem_Ps h i), patOf_succ hi, Function.update_self,
            patOf_update h, ite_eq_left hb1, Nat.or_assoc, mul_assoc]
      · have hc : ¬ (decide (i < cfg.aps.size) && decide (s * getD0 cfg.aps i ≤ cfg.X)) = true := by
          simpa using hcond
        rw [ite_eq_right hc] at hok ⊢
        have hL : L cfg γ i s = {0} := by
          by_cases hi : i < cfg.aps.size
          · exact L_of_gt h γ hsX (by have := fun h' => hcond ⟨hi, h'⟩; simp only [qf]; omega)
          · exact L_of_le (Nat.le_of_not_lt hi) γ hsX
        rw [view_leaf, hL, sum_singleton, smooth_zero, Nat.mul_one, patOf_zero, Nat.or_zero]
        have hlen : len = (s.divisors.filter (· < cfg.M1)).card := by
          have := congrArg Multiset.card hseg
          rw [card_seg, Nat.sub_zero] at this
          exact this
        rw [hτ, hlen, hsig]
        rfl
    · -- an exponent `a ≥ 1` of `q = q_i`
      obtain ⟨hi, hs0, hcop, ha, hX, hbe, hbs, hseg0, hsegb, hsig⟩ := hinv
      subst hq hsa hτ0 hbe
      have hqp : (qf cfg i).Prime := h.prime i hi
      have hq1 : 1 ≤ qf cfg i := hqp.one_lt.le
      have haγ : a ≤ γ (qf cfg i) :=
        hγ i hi a ((Nat.le_mul_of_pos_left _ hs0).trans hX)
      rw [enumExp] at hok ⊢
      obtain ⟨e1, e2, e3, e4⟩ := extendBlock_frame cfg (qf cfg i) be (be - bs + 1) bs be sig2 acc
      have hspec := extendBlock_spec cfg (qf cfg i) be (be - bs + 1) bs be sig2 acc
      generalize extendBlock cfg (qf cfg i) be bs be sig2 acc (be - bs + 1) = r at e1 e2 e3 e4 hspec hok ⊢
      obtain ⟨acc1, len', sig2'⟩ := r
      simp only at e1 e2 e3 e4 hspec hok ⊢
      set acc2 := enumNode cfg f (i + 1) (s * qf cfg i ^ a) (s.divisors.card * (a + 1)) pat len'
        sig2' acc1 with hacc2
      have hok2 : acc2.ok = true := by
        split_ifs at hok
        · exact okE _ _ _ _ _ _ _ _ _ _ _ hok
        · exact hok
      have hok1 : acc1.ok = true := okN _ _ _ _ _ _ _ hok2
      obtain ⟨-, hv1, -, hfr1, hlen, hnew, hsig'⟩ := hspec acc1 len' sig2' rfl le_rfl hok1
      rw [hsegb, filter_map_mul_filter _ hq1, ← pow_succ, Nat.sub_add_cancel ha] at hnew hsig'
      -- the child node `(i+1, s q^a)`
      have hinvN : NodeInv cfg (i + 1) (s * qf cfg i ^ a) (s.divisors.card * (a + 1)) len' sig2'
          acc1.buf :=
        nodeInv_child h hi hs0 hcop ha hX
          (by rw [seg_congr (fun j _ hj => hfr1 j hj), hseg0]) hnew hlen
          (by rw [hsig', hsig])
      have hv2 := ihN (i + 1) (s * qf cfg i ^ a) (s.divisors.card * (a + 1)) pat len' sig2' acc1
        hinvN hok2
      rw [hv1] at hv2
      have hsplit : ∑ b ∈ Ico a (γ (qf cfg i) + 1), ∑ w ∈ L cfg γ (i + 1) (s * qf cfg i ^ b),
            LV cfg (s * qf cfg i ^ b * smooth (Ps cfg (i + 1)) w) (pat ||| patOf cfg (i + 1) w) =
          ∑ w ∈ L cfg γ (i + 1) (s * qf cfg i ^ a),
            LV cfg (s * qf cfg i ^ a * smooth (Ps cfg (i + 1)) w) (pat ||| patOf cfg (i + 1) w) +
          ∑ b ∈ Ico (a + 1) (γ (qf cfg i) + 1), ∑ w ∈ L cfg γ (i + 1) (s * qf cfg i ^ b),
            LV cfg (s * qf cfg i ^ b * smooth (Ps cfg (i + 1)) w) (pat ||| patOf cfg (i + 1) w) :=
        sum_eq_sum_Ico_succ_bot (by omega) _
      rw [hsplit]
      split_ifs at hok ⊢ with hnext
      · -- continue with the exponent `a + 1`
        have hfr2 := (frN (i + 1) (s * qf cfg i ^ a) (s.divisors.card * (a + 1)) pat len' sig2'
          acc1).2
        have hinvE : ExpInv cfg i s (a + 1) be len' len' sig2' acc2.buf := by
          refine ⟨hi, hs0, hcop, by omega, by rw [pow_succ, ← mul_assoc]; exact hnext, rfl, hlen,
            ?_, ?_, ?_⟩
          · rw [seg_congr (fun j _ hj => hfr2 j hj), Nat.add_sub_cancel]
            exact hinvN.2.2.2.2.1
          · rw [seg_congr (fun j _ hj => hfr2 j (by omega)), Nat.add_sub_cancel]
            exact hnew
          · rw [Nat.add_sub_cancel]
            exact hinvN.2.2.2.2.2
        have hvE := ihE i (qf cfg i) (s * qf cfg i ^ a * qf cfg i) (a + 1) s.divisors.card pat be
          len' len' sig2' acc2 s rfl (by rw [pow_succ, mul_assoc]) rfl hinvE hok
        rw [hvE, hv2, add_assoc]
      · -- the exponent loop stops: every further exponent overshoots `X`
        rw [hv2]
        congr 1
        have hz : ∑ b ∈ Ico (a + 1) (γ (qf cfg i) + 1), ∑ w ∈ L cfg γ (i + 1) (s * qf cfg i ^ b),
            LV cfg (s * qf cfg i ^ b * smooth (Ps cfg (i + 1)) w)
              (pat ||| patOf cfg (i + 1) w) = 0 := by
          refine sum_eq_zero fun b hb => ?_
          have hb1 : a + 1 ≤ b := (mem_Ico.1 hb).1
          have hlt : cfg.X < s * qf cfg i ^ b := by
            have h1 : s * qf cfg i ^ (a + 1) ≤ s * qf cfg i ^ b :=
              Nat.mul_le_mul_left s (Nat.pow_le_pow_right hqp.pos hb1)
            rw [pow_succ, ← mul_assoc] at h1
            omega
          rw [L_of_lt h γ hlt, sum_empty]
        rw [hz, add_zero]

end

/-! ### The whole run -/

/-- **Semantics of `runEnum`**: if the run ends with `ok = true`, the five accumulator arrays are
the sums, over the configurations `w` of the A-primes with `s(w) ≤ X` (caps `γ` admitting every
fitting exponent), of the leaf contributions with the true `τ`, `σ₁`, `σ₂` and the pattern
`patOf cfg 0 w`. -/
theorem runEnum_view {cfg : EnumCfg} (h : EnumHyp cfg) {γ : ℕ → ℕ} (hγ : CapOK cfg γ)
    (hX : 1 ≤ cfg.X) (bufSize : ℕ) (hok : (runEnum cfg bufSize).ok = true) :
    view (runEnum cfg bufSize) =
      ∑ w ∈ L cfg γ 0 1, LV cfg (smooth (Ps cfg 0) w) (patOf cfg 0 w) := by
  unfold runEnum at hok ⊢
  simp only at hok ⊢
  have hbuf : getD0 ((Array.replicate (bufSize + 2) 0).set! 0 1) 0 = 1 := by
    rw [getD0_set!, ite_eq_left ⟨rfl, by simp⟩]
  have hinv : NodeInv cfg 0 1 1 (if 1 < cfg.M1 then 1 else 0) (if 1 < cfg.M2 then 1 else 0)
      ((Array.replicate (bufSize + 2) 0).set! 0 1) := by
    refine ⟨Nat.one_pos, hX, fun j _ _ => Nat.coprime_one_right _, by simp, ?_, ?_⟩
    · split_ifs with h1
      · rw [seg_single, hbuf, Nat.divisors_one, filter_singleton, ite_eq_left h1]
        rfl
      · rw [seg_eq_zero le_rfl, Nat.divisors_one, filter_singleton, ite_eq_right h1]
        rfl
    · split_ifs with h1
      · rw [Nat.divisors_one, filter_singleton, ite_eq_left h1, card_singleton]
      · rw [Nat.divisors_one, filter_singleton, ite_eq_right h1, card_empty]
  rw [(enum_view h hγ 100000).1 0 1 1 0 _ _ _ hinv hok]
  have h0 : view ⟨(Array.replicate (bufSize + 2) 0).set! 0 1, #[], #[], #[], #[], #[], 0, true⟩ =
      0 := by
    funext k j
    fin_cases k <;> simp [view]
  rw [h0, zero_add]
  refine sum_congr rfl fun w _ => ?_
  rw [Nat.one_mul, Nat.zero_or]

end MinModulus.CheckerSound.C
