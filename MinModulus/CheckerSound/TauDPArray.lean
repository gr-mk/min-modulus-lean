import MinModulus.CheckerImpl.TauDP
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# `CheckerSound.TauDPArray` (agent CS-B): exact natural-number semantics of the τ-DP loops

Status: complete, no `sorry`.

Pure `ℕ`-level statements about the loops of `CheckerImpl/TauDP.lean` (no rounding analysis,
no probability): what each array entry *is*, as a finite sum. The real-number specifications
(`TauDP.lean`) are derived from these.

* array access: `getElem!_set!`, `getElem!_push`, `getElem!_replicate`, `size_set!`;
* `mkExpLaw`: `mkExpLaw_up`, `mkExpLaw_dn` (entries), `mkExpLaw_lostUp`, `mkExpLaw_acut_le`
  (`acut ≤ 64`), `pow_acut_le` (`q^acut ≤ 2^bits`), `le_acut_of_pow_le`
  (`q^a ≤ 2^bits → a ≤ acut`, for `q ≥ 2`, `bits ≤ 64`), `two_pow_lt_pow_acut_succ`
  (`2^bits < q^(acut+1)`), sizes;
* `dpStep`: `dpStep_size`, `dpStep_get` (push form
  `Dn[T] = Σ_{1 ≤ t < N} Σ_{a ≤ acut} [t(a+1) = T] mulR up D[t] law[a]`, `T < N`);
* `fbTable`: sizes and entries `S0[j] = Σ_{T ≤ j} D[T]`, `PP[j] = Σ_{i < j} ⌈S0[i]/2^20⌉`;
* `buildA.sumK` (`sumK_eq_range`), `buildA.top` (`buildA_top_zero`: `up[k] = 0` for
  `kTop < k ≤ KMAX`).
-/

namespace MinModulus.CheckerSound.B

open MinModulus.CheckerImpl Finset

/-! ### Array access (`Array ℕ`, default value `0`) -/

theorem getElem!_eq_getD0 (xs : Array ℕ) (i : ℕ) : xs[i]! = xs[i]?.getD 0 := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  rfl

theorem getElem!_of_size_le (xs : Array ℕ) {i : ℕ} (h : xs.size ≤ i) : xs[i]! = 0 := by
  rw [getElem!_eq_getD0, Array.getElem?_eq_none h]
  rfl

theorem size_set! (xs : Array ℕ) (i v : ℕ) : (xs.set! i v).size = xs.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem getElem!_set! (xs : Array ℕ) (i v j : ℕ) :
    (xs.set! i v)[j]! = if i = j ∧ i < xs.size then v else xs[j]! := by
  rw [getElem!_eq_getD0, getElem!_eq_getD0, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < xs.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem getElem!_push (xs : Array ℕ) (x j : ℕ) :
    (xs.push x)[j]! = if j = xs.size then x else xs[j]! := by
  rw [getElem!_eq_getD0, getElem!_eq_getD0, Array.getElem?_push]
  split_ifs <;> simp

theorem getElem!_replicate (n v j : ℕ) :
    (Array.replicate n v)[j]! = if j < n then v else 0 := by
  rw [getElem!_eq_getD0, Array.getElem?_replicate]
  split_ifs <;> simp

/-- The initial DP array: `τ = 1` surely. -/
theorem getElem!_init (n j : ℕ) (h1 : 1 < n) :
    ((Array.replicate n 0).set! 1 ONE)[j]! = if j = 1 then ONE else 0 := by
  rw [getElem!_set!, getElem!_replicate, Array.size_replicate]
  by_cases hj : j = 1
  · subst hj; simp [h1]
  · have : ¬ (1 = j ∧ 1 < n) := fun h => hj h.1.symm
    rw [ite_eq_right this, ite_eq_right hj]
    split_ifs <;> rfl

theorem size_init (n : ℕ) : ((Array.replicate n 0).set! 1 ONE).size = n := by
  rw [size_set!, Array.size_replicate]

/-! ### `mulR` -/

theorem zero_lt_ONE : 0 < ONE := by rw [ONE_eq]; positivity

theorem mulUp_zero_left (y : ℕ) : mulUp 0 y = 0 := by
  unfold mulUp
  rw [Nat.zero_mul, Nat.zero_add]
  exact Nat.div_eq_of_lt (Nat.sub_lt zero_lt_ONE Nat.one_pos)

theorem mulDn_zero_left (y : ℕ) : mulDn 0 y = 0 := by
  unfold mulDn
  rw [Nat.zero_mul, Nat.zero_div]

theorem mulR_zero_left (up : Bool) (y : ℕ) : mulR up 0 y = 0 := by
  unfold mulR
  split
  · exact mulUp_zero_left y
  · exact mulDn_zero_left y

/-! ### `dpStep` -/

theorem dpStep_inner_size (up : Bool) (N : ℕ) (law : Array ℕ) (d t a f : ℕ) (Dn : Array ℕ) :
    (dpStep.inner up N law d t a f Dn).size = Dn.size := by
  induction f generalizing a Dn with
  | zero => rfl
  | succ f ih =>
    rw [dpStep.inner.eq_2]
    split_ifs
    · rw [ih, size_set!]
    · rfl

/-- The inner loop adds `mulR up d law[a']` at `t(a'+1)` for `a' ∈ [a, a + f)` (the early exit
drops only indices `≥ N`). -/
theorem dpStep_inner_get (up : Bool) (N : ℕ) (law : Array ℕ) (d t a f : ℕ) (Dn : Array ℕ)
    (hN : Dn.size = N) {T : ℕ} (hT : T < N) :
    (dpStep.inner up N law d t a f Dn)[T]! =
      Dn[T]! + ∑ a' ∈ Ico a (a + f), if t * (a' + 1) = T then mulR up d law[a']! else 0 := by
  induction f generalizing a Dn with
  | zero => simp [dpStep.inner.eq_1]
  | succ f ih =>
    rw [dpStep.inner.eq_2]
    split_ifs with h
    · rw [ih (a + 1) _ (by rw [size_set!, hN]), getElem!_set!,
        sum_eq_sum_Ico_succ_bot (by omega : a < a + (f + 1)),
        show a + 1 + f = a + (f + 1) by omega]
      by_cases hTa : t * (a + 1) = T
      · rw [ite_eq_left ⟨hTa, by omega⟩, ite_eq_left hTa, hTa]
        omega
      · rw [ite_eq_right (fun h' => hTa h'.1), ite_eq_right hTa]
        omega
    · have hz : ∀ a' ∈ Ico a (a + (f + 1)),
          (if t * (a' + 1) = T then mulR up d law[a']! else 0) = 0 := by
        intro a' ha'
        have h1 : t * (a + 1) ≤ t * (a' + 1) :=
          Nat.mul_le_mul_left _ (by simp only [mem_Ico] at ha'; omega)
        rw [ite_eq_right (by omega)]
      rw [sum_congr rfl hz, sum_const_zero, Nat.add_zero]

theorem dpStep_outer_size (up : Bool) (D : Array ℕ) (N : ℕ) (law : Array ℕ) (acut t f : ℕ)
    (Dn : Array ℕ) : (dpStep.outer up D N law acut t f Dn).size = Dn.size := by
  induction f generalizing t Dn with
  | zero => rfl
  | succ f ih =>
    rw [dpStep.outer.eq_2, ih]
    split_ifs
    · rfl
    · rw [dpStep_inner_size]

theorem dpStep_outer_get (up : Bool) (D : Array ℕ) (N : ℕ) (law : Array ℕ) (acut t f : ℕ)
    (Dn : Array ℕ) (hN : Dn.size = N) {T : ℕ} (hT : T < N) :
    (dpStep.outer up D N law acut t f Dn)[T]! =
      Dn[T]! + ∑ t' ∈ Ico t (t + f), ∑ a ∈ range (acut + 1),
        if t' * (a + 1) = T then mulR up D[t']! law[a]! else 0 := by
  induction f generalizing t Dn with
  | zero => simp [dpStep.outer.eq_1]
  | succ f ih =>
    have hsz : (if (D[t]! == 0) = true then Dn else
        dpStep.inner up N law D[t]! t 0 (acut + 1) Dn).size = N := by
      split_ifs
      · exact hN
      · rw [dpStep_inner_size, hN]
    rw [dpStep.outer.eq_2, ih (t + 1) _ hsz, sum_eq_sum_Ico_succ_bot (by omega : t < t + (f + 1)),
      show t + 1 + f = t + (f + 1) by omega]
    by_cases hd : D[t]! = 0
    · have hz : ∑ a ∈ range (acut + 1),
          (if t * (a + 1) = T then mulR up D[t]! law[a]! else 0) = 0 := by
        refine sum_eq_zero fun a _ => ?_
        rw [hd, mulR_zero_left]
        split_ifs <;> rfl
      rw [ite_eq_left (by simp [hd]), hz]
      omega
    · rw [ite_eq_right (by simp [hd]), dpStep_inner_get up N law _ t 0 _ Dn hN hT, Nat.zero_add,
        ← range_eq_Ico]
      omega

theorem dpStep_size (up : Bool) (D : Array ℕ) (N : ℕ) (law : Array ℕ) (acut : ℕ) :
    (dpStep up D N law acut).size = N := by
  unfold dpStep
  rw [dpStep_outer_size, Array.size_replicate]

/-- **`dpStep` semantics** (push form, exact): for `T < N`,
`Dn[T] = Σ_{1 ≤ t < N} Σ_{a ≤ acut} [t (a+1) = T] mulR up D[t] law[a]`. -/
theorem dpStep_get (up : Bool) (D : Array ℕ) (N : ℕ) (law : Array ℕ) (acut : ℕ) {T : ℕ}
    (hT : T < N) :
    (dpStep up D N law acut)[T]! =
      ∑ t ∈ Ico 1 N, ∑ a ∈ range (acut + 1),
        if t * (a + 1) = T then mulR up D[t]! law[a]! else 0 := by
  unfold dpStep
  rw [dpStep_outer_get up D N law acut 1 (N - 1) _ Array.size_replicate hT, getElem!_replicate,
    ite_eq_left hT, Nat.zero_add, show 1 + (N - 1) = N by omega]

/-! ### `mkExpLaw` -/

/-- The upper entries of `mkExpLaw q dn bits` (`nd = 10^9 − dn`). -/
def expUpE (q nd a : ℕ) : ℕ :=
  if a = 0 then ratUp (q * nd - DDEN) (q * nd) else ratUp (DDEN * (q - 1)) (nd * q ^ (a + 1))

/-- The lower entries of `mkExpLaw q dn bits`. -/
def expDnE (q nd a : ℕ) : ℕ :=
  if a = 0 then ratDn (q * nd - DDEN) (q * nd) else ratDn (DDEN * (q - 1)) (nd * q ^ (a + 1))

/-- Loop invariant of `mkExpLaw.go`. -/
theorem mkExpLaw_go_spec (q nd lim : ℕ) (f : ℕ) :
    ∀ (a : ℕ) (up dn : Array ℕ), 1 ≤ a → a + f = 65 → up.size = a → dn.size = a →
      (∀ i < a, up[i]! = expUpE q nd i ∧ dn[i]! = expDnE q nd i) → q ^ (a - 1) ≤ lim →
      let L := mkExpLaw.go q nd lim a (q ^ a) up dn f
      L.acut ≤ 64 ∧ (∀ i ≤ L.acut, L.up[i]! = expUpE q nd i ∧ L.dn[i]! = expDnE q nd i) ∧
        L.lostUp = ratUp DDEN (nd * q ^ (L.acut + 1)) ∧ q ^ L.acut ≤ lim ∧
        (L.acut = 64 ∨ lim < q ^ (L.acut + 1)) ∧ L.up.size = L.acut + 1 ∧
        L.dn.size = L.acut + 1 := by
  induction f with
  | zero =>
    intro a up dn ha1 ha hup hdn hent hlim
    simp only [mkExpLaw.go]
    have ha' : a = 65 := by omega
    subst ha'
    refine ⟨by omega, fun i hi => hent i (by omega), rfl, hlim, Or.inl rfl, hup, hdn⟩
  | succ f ih =>
    intro a up dn ha1 ha hup hdn hent hlim
    rw [mkExpLaw.go.eq_2]
    split_ifs with hq
    · simp only
      have e : q ^ a * q = q ^ (a + 1) := (pow_succ q a).symm
      rw [e]
      refine ih (a + 1) _ _ (by omega) (by omega) (by rw [Array.size_push, hup])
        (by rw [Array.size_push, hdn]) (fun i hi => ?_) (by simpa using hq)
      rw [getElem!_push, getElem!_push, hup, hdn]
      by_cases hia : i = a
      · subst hia
        have : i ≠ 0 := by omega
        simp [expUpE, expDnE, this, pow_succ]
      · rw [ite_eq_right hia, ite_eq_right hia]
        exact hent i (by omega)
    · dsimp only
      refine ⟨by omega, fun i hi => hent i (by omega), ?_, hlim, Or.inr ?_, by omega, by omega⟩
      · rw [show a - 1 + 1 = a by omega]
      · rw [show a - 1 + 1 = a by omega]
        omega

theorem mkExpLaw_eq (q dn bits : ℕ) :
    mkExpLaw q dn bits = mkExpLaw.go q (nuDen dn) (2 ^ bits) 1 (q ^ 1)
      #[ratUp (q * nuDen dn - DDEN) (q * nuDen dn)] #[ratDn (q * nuDen dn - DDEN) (q * nuDen dn)]
      64 := by
  rw [mkExpLaw, Nat.one_shiftLeft, pow_one]

theorem mkExpLaw_spec (q dn bits : ℕ) :
    let L := mkExpLaw q dn bits
    L.acut ≤ 64 ∧ (∀ i ≤ L.acut, L.up[i]! = expUpE q (nuDen dn) i ∧
        L.dn[i]! = expDnE q (nuDen dn) i) ∧
      L.lostUp = ratUp DDEN (nuDen dn * q ^ (L.acut + 1)) ∧ q ^ L.acut ≤ 2 ^ bits ∧
      (L.acut = 64 ∨ 2 ^ bits < q ^ (L.acut + 1)) ∧ L.up.size = L.acut + 1 ∧
      L.dn.size = L.acut + 1 := by
  rw [mkExpLaw_eq]
  exact mkExpLaw_go_spec q (nuDen dn) (2 ^ bits) 64 1 #[ratUp (q * nuDen dn - DDEN) (q * nuDen dn)]
    #[ratDn (q * nuDen dn - DDEN) (q * nuDen dn)] le_rfl rfl rfl rfl
    (fun i hi => by
      have : i = 0 := by omega
      subst this
      simp [expUpE, expDnE])
    (by rw [Nat.sub_self, pow_zero]; exact Nat.one_le_two_pow)

theorem mkExpLaw_acut_le (q dn bits : ℕ) : (mkExpLaw q dn bits).acut ≤ 64 :=
  (mkExpLaw_spec q dn bits).1

theorem mkExpLaw_up (q dn bits : ℕ) {i : ℕ} (hi : i ≤ (mkExpLaw q dn bits).acut) :
    (mkExpLaw q dn bits).up[i]! = expUpE q (nuDen dn) i :=
  ((mkExpLaw_spec q dn bits).2.1 i hi).1

theorem mkExpLaw_dn (q dn bits : ℕ) {i : ℕ} (hi : i ≤ (mkExpLaw q dn bits).acut) :
    (mkExpLaw q dn bits).dn[i]! = expDnE q (nuDen dn) i :=
  ((mkExpLaw_spec q dn bits).2.1 i hi).2

theorem mkExpLaw_lostUp (q dn bits : ℕ) :
    (mkExpLaw q dn bits).lostUp = ratUp DDEN (nuDen dn * q ^ ((mkExpLaw q dn bits).acut + 1)) :=
  (mkExpLaw_spec q dn bits).2.2.1

/-- `q ^ acut ≤ 2 ^ bits`. -/
theorem pow_acut_le (q dn bits : ℕ) : q ^ (mkExpLaw q dn bits).acut ≤ 2 ^ bits :=
  (mkExpLaw_spec q dn bits).2.2.2.1

theorem mkExpLaw_up_size (q dn bits : ℕ) :
    (mkExpLaw q dn bits).up.size = (mkExpLaw q dn bits).acut + 1 :=
  (mkExpLaw_spec q dn bits).2.2.2.2.2.1

theorem mkExpLaw_dn_size (q dn bits : ℕ) :
    (mkExpLaw q dn bits).dn.size = (mkExpLaw q dn bits).acut + 1 :=
  (mkExpLaw_spec q dn bits).2.2.2.2.2.2

/-- **Every exponent with `q^a ≤ 2^bits` is kept** (`q ≥ 2`, `bits ≤ 64`): `a ≤ acut`. -/
theorem le_acut_of_pow_le {q : ℕ} (hq : 2 ≤ q) (dn : ℕ) {bits : ℕ} (hbits : bits ≤ 64) {a : ℕ}
    (ha : q ^ a ≤ 2 ^ bits) : a ≤ (mkExpLaw q dn bits).acut := by
  rcases (mkExpLaw_spec q dn bits).2.2.2.2.1 with h | h
  · rw [h]
    by_contra hlt
    have h1 : 2 ^ 65 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ a ≤ q ^ a := Nat.pow_le_pow_left hq a
    have h3 : 2 ^ bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hbits
    have h4 : (2 : ℕ) ^ 64 < 2 ^ 65 := by norm_num
    omega
  · by_contra hlt
    have : q ^ ((mkExpLaw q dn bits).acut + 1) ≤ q ^ a :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- **The first dropped exponent exceeds the bound** (`q ≥ 2`, `bits ≤ 64`):
`2^bits < q^(acut + 1)`. -/
theorem two_pow_lt_pow_acut_succ {q : ℕ} (hq : 2 ≤ q) (dn : ℕ) {bits : ℕ} (hbits : bits ≤ 64) :
    2 ^ bits < q ^ ((mkExpLaw q dn bits).acut + 1) := by
  rcases (mkExpLaw_spec q dn bits).2.2.2.2.1 with h | h
  · rw [h]
    have h2 : 2 ^ 65 ≤ q ^ (64 + 1) := Nat.pow_le_pow_left hq 65
    have h3 : 2 ^ bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hbits
    have h4 : (2 : ℕ) ^ 64 < 2 ^ 65 := by norm_num
    omega
  · exact h

/-! ### `fbTable` -/

/-- `S0[j] = Σ_{T ≤ j} D[T]`. -/
def S0val (D : Array ℕ) (j : ℕ) : ℕ := ∑ T ∈ range (j + 1), D[T]!

/-- `PP[j] = Σ_{i < j} ⌈S0[i]/2^20⌉`. -/
def PPval (D : Array ℕ) (j : ℕ) : ℕ := ∑ i ∈ range j, (S0val D i + 1048575) >>> 20

theorem fbTable_go_spec (D : Array ℕ) (f : ℕ) :
    ∀ (j s0 pp : ℕ) (S0 PP : Array ℕ), S0.size = j → PP.size = j →
      s0 = ∑ T ∈ range j, D[T]! → pp = PPval D j →
      (∀ i < j, S0[i]! = S0val D i ∧ PP[i]! = PPval D i) →
      let R := fbTable.go D j s0 pp S0 PP f
      R.1.size = j + f ∧ R.2.size = j + f ∧
        ∀ i < j + f, R.1[i]! = S0val D i ∧ R.2[i]! = PPval D i := by
  induction f with
  | zero =>
    intro j s0 pp S0 PP hS hP _ _ hent
    simp only [fbTable.go, Nat.add_zero]
    exact ⟨hS, hP, hent⟩
  | succ f ih =>
    intro j s0 pp S0 PP hS hP hs0 hpp hent
    simp only [fbTable.go]
    have hs0' : s0 + D[j]! = S0val D j := by
      rw [S0val, sum_range_succ, hs0]
    have h := ih (j + 1) (s0 + D[j]!) (pp + ((s0 + D[j]! + 1048575) >>> 20)) (S0.push (s0 + D[j]!))
      (PP.push pp) (by rw [Array.size_push, hS]) (by rw [Array.size_push, hP])
      (by rw [sum_range_succ, hs0]) (by rw [hpp, PPval, PPval, sum_range_succ, hs0'])
      (fun i hi => by
        rw [getElem!_push, getElem!_push, hS, hP]
        by_cases hij : i = j
        · subst hij
          simp [hs0', hpp]
        · rw [ite_eq_right hij, ite_eq_right hij]
          exact hent i (by omega))
    rw [show j + 1 + f = j + (f + 1) by omega] at h
    exact h

theorem fbTable_spec (D : Array ℕ) (K : ℕ) :
    (fbTable D K).1.size = K + 1 ∧ (fbTable D K).2.size = K + 1 ∧
      ∀ i ≤ K, (fbTable D K).1[i]! = S0val D i ∧ (fbTable D K).2[i]! = PPval D i := by
  have h := fbTable_go_spec D (K + 1) 0 0 0 (Array.emptyWithCapacity (K + 1))
    (Array.emptyWithCapacity (K + 1)) (by simp) (by simp) (by simp) (by simp [PPval])
    (fun i hi => absurd hi (Nat.not_lt_zero i))
  rw [Nat.zero_add] at h
  exact ⟨h.1, h.2.1, fun i hi => h.2.2 i (by omega)⟩

/-! ### `buildA.sumK`, `buildA.top` -/

theorem sumK_eq (dn : Array ℕ) (f : ℕ) :
    ∀ k acc : ℕ, buildA.sumK dn k acc f = acc + ∑ j ∈ Ico k (k + f), j * dn[j]! := by
  induction f with
  | zero => intro k acc; simp [buildA.sumK]
  | succ f ih =>
    intro k acc
    simp only [buildA.sumK]
    rw [ih, sum_eq_sum_Ico_succ_bot (by omega : k < k + (f + 1)),
      show k + 1 + f = k + (f + 1) by omega]
    omega

/-- `sumK dn 1 0 KMAX = Σ_{k ≤ KMAX} k·dn[k]`. -/
theorem sumK_eq_range (dn : Array ℕ) (KMAX : ℕ) :
    buildA.sumK dn 1 0 KMAX = ∑ k ∈ range (KMAX + 1), k * dn[k]! := by
  rw [sumK_eq, Nat.zero_add, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < KMAX + 1),
    Nat.zero_mul, Nat.zero_add, Nat.add_comm]

theorem buildA_top_spec (up : Array ℕ) (KMAX : ℕ) (f : ℕ) :
    ∀ k : ℕ, k ≤ KMAX → k ≤ f → (∀ j, k < j → j ≤ KMAX → up[j]! = 0) →
      ∀ j, buildA.top up k f < j → j ≤ KMAX → up[j]! = 0 := by
  induction f with
  | zero =>
    intro k _ _ hk j hj hjK
    exact hk j hj hjK
  | succ f ih =>
    intro k hkK hkf hk j hj hjK
    simp only [buildA.top] at hj
    split_ifs at hj with h0
    · by_cases hk0 : k = 0
      · subst hk0
        exact hk j (by omega) hjK
      · refine ih (k - 1) (by omega) (by omega) (fun j' hj' hj'K => ?_) j hj hjK
        by_cases hjk : j' = k
        · subst hjk
          simpa using h0
        · exact hk j' (by omega) hj'K
    · exact hk j hj hjK

/-- **`kTop`**: every `k` with `kTop < k ≤ KMAX` has `up[k] = 0`. -/
theorem buildA_top_zero (up : Array ℕ) (KMAX : ℕ) {j : ℕ} (hj : buildA.top up KMAX KMAX < j)
    (hjK : j ≤ KMAX) : up[j]! = 0 :=
  buildA_top_spec up KMAX KMAX KMAX le_rfl le_rfl (fun j h1 h2 => absurd h2 (by omega)) j hj hjK

end MinModulus.CheckerSound.B
