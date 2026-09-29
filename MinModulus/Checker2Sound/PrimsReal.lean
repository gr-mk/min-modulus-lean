import MinModulus.Checker2Sound.Defs
import MinModulus.Checker2Sound.PrimsArray
import MinModulus.CheckerSound.TauDPReal
import MinModulus.CheckerSound.Sieve
import MinModulus.CheckerMath.ImplBridge

/-!
# `Checker2Sound.PrimsReal` (agent L2-C): the code primitives in real terms

STATUS: complete, no `sorry` (agent L2-C, lean2 stage 2). Axioms: `propext`, `Classical.choice`,
`Quot.sound`.

P-values `pv x = x/2^62`, W-values `wv x = x/2^48` (`Checker2Sound.Defs`). Namespace
`MinModulus.Checker2Sound.C`.

* `pv`: `pv_nonneg`, `pv_zero`, `pv_ONE2`, `pv_add`, `pv_sum`, `pv_natMul`, `pv_mulUp`
  (`pv x · pv y ≤ pv (mulUp x y)`), `pv_mono`;
* the certificate's tilts: `deltaN2_lt`, `two_deltaN2_le`, `nu2_eq_tiltN` (`nu2 P q = 10^9/(10^9 − dn)`
  for `q ≤ X`, i.e. `CheckerSound.B.tiltN (deltaN2 P q)`), `nu2_mem` (`0 ≤ ν ≤ q`), `one_le_nu2`,
  `nu2_le_two`;
* one-prime bounds: `pmass_le_pmE` (`P(v = a) ≤ pv (pmE q dn a)`, every `a`), `rho_le_pmArr`
  (every cap `γ > a`), `hMass_le_hUp` (`h_γ(A) ≤ pv (hUp q dn A)`, `A ≥ 1`), `facE1u_ge`
  (`1 + ν/(q−1) ≤ pv (facE1u q dn)`), `expect1_add_one_le_facE1u`;
* `idxSet`: `mem_idxSet`, `idxSet_self`, `idxSet_succ`, `getElem_notMem_idxSet`, `idxSet_mem`
  (primes `≤ PX`).
-/

namespace MinModulus.Checker2Sound.C

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Main MinModulus.Smooth MinModulus.Checker2Sound

/-! ### P-values -/

theorem two_pow_62_pos' : (0 : ℝ) < 2 ^ 62 := by positivity

theorem cast_ONE2 : ((ONE2 : ℕ) : ℝ) = 2 ^ 62 := by
  rw [ONE2_eq, ONE_eq]
  push_cast
  ring

theorem pv_nonneg (x : ℕ) : 0 ≤ pv x := by unfold pv; positivity

@[simp] theorem pv_zero : pv 0 = 0 := by simp [pv]

theorem pv_ONE2 : pv ONE2 = 1 := by
  unfold pv
  rw [cast_ONE2, div_self (by positivity)]

theorem pv_add (x y : ℕ) : pv (x + y) = pv x + pv y := by
  unfold pv
  push_cast
  ring

theorem pv_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) : pv (∑ i ∈ s, f i) = ∑ i ∈ s, pv (f i) := by
  unfold pv
  rw [Nat.cast_sum, sum_div]

theorem pv_natMul (a x : ℕ) : pv (a * x) = (a : ℝ) * pv x := by
  unfold pv
  push_cast
  ring

theorem pv_mono {x y : ℕ} (h : x ≤ y) : pv x ≤ pv y := by
  unfold pv
  have : (x : ℝ) ≤ y := by exact_mod_cast h
  exact div_le_div_of_nonneg_right this (by positivity)

/-- `mulUp` rounds up: `pv x · pv y ≤ pv (mulUp x y)`. -/
theorem pv_mulUp (x y : ℕ) : pv x * pv y ≤ pv (mulUp x y) := by
  have h := mulUp_ge x y
  unfold pv
  rw [ONE_real] at h
  exact h

theorem pv_ite {c : Prop} [Decidable c] (x : ℕ) : pv (if c then x else 0) = if c then pv x else 0 := by
  split_ifs <;> simp

/-- `ratUp2` rounds up: `num/den ≤ pv (ratUp2 num den)`. -/
theorem pv_ratUp2 {num den : ℕ} (h : 0 < den) : (num : ℝ) / den ≤ pv (ratUp2 num den) := by
  have h1 := ratUp_ge (num := num) h
  unfold pv
  rw [ratUp2_eq]
  rw [ONE_real] at h1
  exact h1

/-- `cdiv` rounds up: `pv x / b ≤ pv (cdiv x b)`. -/
theorem pv_cdiv {x b : ℕ} (hb : 0 < b) : pv x / b ≤ pv (cdiv x b) := by
  have h := cdiv_ge (a := x) hb
  unfold pv
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_div, mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right h (by positivity)

/-! ### The certificate's tilts -/

theorem deltaN2_lt (P : Params2) (q : ℕ) : deltaN2 P q < DDEN := by
  have := deltaN2_le P q
  unfold DNMAX2 at this
  unfold DDEN
  omega

theorem two_deltaN2_le (P : Params2) (q : ℕ) : 2 * deltaN2 P q ≤ DDEN := by
  have := deltaN2_le P q
  unfold DNMAX2 at this
  unfold DDEN
  omega

theorem deltaCert2_of_le {P : Params2} {q : ℕ} (hq : q ≤ P.X) :
    deltaCert2 P q = (deltaN2 P q, DDEN) := by
  unfold deltaCert2
  rw [ite_eq_right (by omega)]

/-- For `q ≤ X`: `δ_q = deltaN2 P q / 10^9`. -/
theorem delta2_of_le {P : Params2} {q : ℕ} (hq : q ≤ P.X) :
    delta2 P q = (deltaN2 P q : ℝ) / 10 ^ 9 := by
  unfold delta2
  rw [deltaPairR_of_eq (deltaCert2_of_le hq), MinModulus.CheckerSound.B.cast_DDEN]

/-- For `q ≤ X`: the certificate's tilt is the checker's exact tilt `10^9/(10^9 − dn)`. -/
theorem nu2_eq_tiltN {P : Params2} {q : ℕ} (hq : q ≤ P.X) :
    nu2 P q = MinModulus.CheckerSound.B.tiltN (deltaN2 P q) := by
  unfold nu2 tilt MinModulus.CheckerSound.B.tiltN
  rw [delta2_of_le hq]

theorem one_le_nu2 {P : Params2} {q : ℕ} (hq : q ≤ P.X) : 1 ≤ nu2 P q := by
  rw [nu2_eq_tiltN hq]
  exact MinModulus.CheckerSound.B.one_le_tiltN _ (two_deltaN2_le P q)

theorem nu2_le_two {P : Params2} {q : ℕ} (hq : q ≤ P.X) : nu2 P q ≤ 2 := by
  rw [nu2_eq_tiltN hq]
  exact MinModulus.CheckerSound.B.tiltN_le_two _ (two_deltaN2_le P q)

theorem nu2_nonneg {P : Params2} {q : ℕ} (hq : q ≤ P.X) : 0 ≤ nu2 P q :=
  zero_le_one.trans (one_le_nu2 hq)

/-- `Smooth`'s standing hypothesis `0 ≤ ν_q ≤ q` for `2 ≤ q ≤ X`. -/
theorem nu2_mem {P : Params2} {q : ℕ} (hq2 : 2 ≤ q) (hq : q ≤ P.X) :
    0 ≤ nu2 P q ∧ nu2 P q ≤ q := by
  have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  exact ⟨nu2_nonneg hq, (nu2_le_two hq).trans h2⟩

/-! ### One-prime bounds: point masses, `h(A)`, `E[v+1]` -/

open MinModulus.CheckerSound.B in
/-- `P(v = a+1) = P(v = a)/q` for `a ≥ 1`. -/
theorem pmass_succ {q : ℕ} {ν : ℝ} {a : ℕ} (ha : a ≠ 0) :
    pmass q ν (a + 1) = pmass q ν a / q := by
  unfold pmass
  rw [ite_eq_right (by omega), ite_eq_right ha, pow_succ]
  ring

open MinModulus.CheckerSound.B in
/-- **`pmArr` entries are upper bounds of the point masses** (every `a`, `q ≥ 2`, `2 dn ≤ 10^9`):
`P(v = a) ≤ pv (pmE q dn a)`. -/
theorem pmass_le_pmE {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) :
    ∀ a, pmass q (tiltN dn) a ≤ pv (pmE q dn a)
  | 0 => by
    have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
    rw [pmass_zero_eq hq h]
    exact pv_ratUp2 (Nat.mul_pos (by omega) (nuDen_pos hlt))
  | 1 => by
    have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
    rw [pmass_pos_eq hq h (by omega)]
    have e : nuDen dn * q ^ (1 + 1) = nuDen dn * q * q := by ring
    rw [e]
    exact pv_ratUp2 (Nat.mul_pos (Nat.mul_pos (nuDen_pos hlt) (by omega)) (by omega))
  | a + 2 => by
    rw [pmass_succ (by omega), pmE_succ_succ]
    have ih := pmass_le_pmE hq h (a + 1)
    have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    exact (div_le_div_of_nonneg_right ih hq'.le).trans (pv_cdiv (by omega))

open MinModulus.CheckerSound.B in
/-- **`pmArr`, every cap `γ > a`**: `ρ(q, ν, γ, a) ≤ pv (pmArr q dn A)[a]` for `a ≤ A`. -/
theorem rho_le_pmArr {q dn A : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) {γ a : ℕ} (ha : a ≤ A)
    (haγ : a < γ) : rho q (tiltN dn) γ a ≤ pv (pmArr q dn A)[a]! := by
  rw [rho_eq_pmass haγ, pmArr_get q dn A ha]
  exact pmass_le_pmE hq h a

open MinModulus.CheckerSound.B in
/-- **`hUp`** (`A ≥ 1`, every cap): `h_γ(A) = E[(v+1)1{v ≥ A}] ≤ pv (hUp q dn A)`. -/
theorem hMass_le_hUp {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) {A : ℕ} (hA : 1 ≤ A) (γ : ℕ) :
    hMass q (tiltN dn) γ A ≤ pv (hUp q dn A) := by
  have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
  have hnd := nuDen_pos hlt
  refine (expect1_hA_le (by omega) (tiltN_mem hq h).1 hA γ).trans ?_
  unfold hUp
  rw [ite_eq_right (by omega)]
  refine le_of_eq_of_le ?_ (pv_ratUp2 (Nat.mul_pos (Nat.mul_pos hnd (pow_pos (by omega) _))
    (by omega)))
  rw [tiltN_eq_div_nuDen hlt]
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1' : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hnd0 : (0 : ℝ) < ((nuDen dn : ℕ) : ℝ) := by exact_mod_cast hnd
  push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
  rw [cast_DDEN]
  simp only [inv_pow]
  field_simp

open MinModulus.CheckerSound.B in
/-- `facE1u` rounds up: `1 + ν/(q−1) ≤ pv (facE1u q dn)`. -/
theorem facE1u_ge {q dn : ℕ} (hq : 2 ≤ q) (h : dn < DDEN) :
    1 + tiltN dn / ((q : ℝ) - 1) ≤ pv (facE1u q dn) := by
  have := facE1_ge hq h
  unfold pv
  rw [facE1u_eq]
  exact this

open MinModulus.CheckerSound.B in
/-- `E_γ[v + 1] ≤ pv (facE1u q dn)`, every cap. -/
theorem expect1_add_one_le_facE1u {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) (γ : ℕ) :
    expect1 q (tiltN dn) γ (fun a => (a : ℝ) + 1) ≤ pv (facE1u q dn) := by
  have hlt : dn < DDEN := by unfold DDEN at h ⊢; omega
  exact (expect1_add_one_le (by omega) (tiltN_mem hq h).1 γ).trans (facE1u_ge hq hlt)

open MinModulus.CheckerSound.B in
/-- `h_γ(0) = E_γ[v + 1] ≤ pv (hUp q dn 0) = pv (facE1u q dn)`. -/
theorem hMass_zero_le_hUp {q dn : ℕ} (hq : 2 ≤ q) (h : 2 * dn ≤ DDEN) (γ : ℕ) :
    hMass q (tiltN dn) γ 0 ≤ pv (hUp q dn 0) := by
  have e : hMass q (tiltN dn) γ 0 = expect1 q (tiltN dn) γ (fun a => (a : ℝ) + 1) := by
    unfold hMass
    simp
  rw [e]
  unfold hUp
  rw [ite_eq_left rfl]
  exact expect1_add_one_le_facE1u hq h γ

/-! ### The same bounds with the certificate's tilts `nu2 P q` (`q ≤ X`) -/

/-- `ν_q = 10^9/(10^9 − deltaN2 P q)` for `q ≤ X`. -/
theorem nu2_eq_div {P : Params2} {q : ℕ} (hq : q ≤ P.X) :
    nu2 P q = (10 : ℝ) ^ 9 / ((10 : ℝ) ^ 9 - deltaN2 P q) := by
  rw [nu2_eq_tiltN hq, MinModulus.CheckerSound.B.tiltN_eq (deltaN2_lt P q)]

/-- **`pmArr`** (every cap `N > a`): `ρ(q, ν_q, N, a) ≤ pv (pmArr q (deltaN2 P q) A)[a]` for `a ≤ A`. -/
theorem rho_nu2_le_pmArr {P : Params2} {q : ℕ} (hq2 : 2 ≤ q) (hqX : q ≤ P.X) {A N a : ℕ}
    (ha : a ≤ A) (haN : a < N) : rho q (nu2 P q) N a ≤ pv (pmArr q (deltaN2 P q) A)[a]! := by
  rw [nu2_eq_tiltN hqX]
  exact rho_le_pmArr hq2 (two_deltaN2_le P q) ha haN

/-- **`hArr`** (every cap): `h_N(a) ≤ pv (hArr q (deltaN2 P q) A)[a]` for `a ≤ A` (including `a = 0`). -/
theorem hMass_nu2_le_hArr {P : Params2} {q : ℕ} (hq2 : 2 ≤ q) (hqX : q ≤ P.X) {A a : ℕ}
    (ha : a ≤ A) (N : ℕ) : hMass q (nu2 P q) N a ≤ pv (hArr q (deltaN2 P q) A)[a]! := by
  rw [hArr_get _ _ _ ha, nu2_eq_tiltN hqX]
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · exact hMass_zero_le_hUp hq2 (two_deltaN2_le P q) N
  · exact hMass_le_hUp hq2 (two_deltaN2_le P q) ha1 N

/-- `1 + ν_q/(q−1) ≤ pv (facE1u q (deltaN2 P q))`. -/
theorem facE1u_nu2_ge {P : Params2} {q : ℕ} (hq2 : 2 ≤ q) (hqX : q ≤ P.X) :
    1 + nu2 P q / ((q : ℝ) - 1) ≤ pv (facE1u q (deltaN2 P q)) := by
  rw [nu2_eq_tiltN hqX]
  exact facE1u_ge hq2 (deltaN2_lt P q)

/-- `E_N[v + 1] ≤ pv (facE1u q (deltaN2 P q))`, every cap. -/
theorem expect1_add_one_nu2_le {P : Params2} {q : ℕ} (hq2 : 2 ≤ q) (hqX : q ≤ P.X) (N : ℕ) :
    expect1 q (nu2 P q) N (fun a => (a : ℝ) + 1) ≤ pv (facE1u q (deltaN2 P q)) := by
  rw [nu2_eq_tiltN hqX]
  exact expect1_add_one_le_facE1u hq2 (two_deltaN2_le P q) N

/-! ### `e2Up`, `h2Up` (the e-law, `q ≥ 3`) -/

open MinModulus.CheckerSound.B in
/-- `e2Up` rounds up: `1 + ν/(q−2) ≤ pv (e2Up q dn)` (`q ≥ 3`). -/
theorem e2Up_ge {q dn : ℕ} (hq : 3 ≤ q) (h : dn < DDEN) :
    1 + tiltN dn / ((q : ℝ) - 2) ≤ pv (e2Up q dn) := by
  have hnd := nuDen_pos h
  have hq2 : 0 < q - 2 := by omega
  unfold e2Up
  refine le_of_eq_of_le ?_ (pv_ratUp2 (Nat.mul_pos hq2 hnd))
  rw [tiltN_eq_div_nuDen h]
  have hq2' : (0 : ℝ) < (q : ℝ) - 2 := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hnd0 : (0 : ℝ) < ((nuDen dn : ℕ) : ℝ) := by exact_mod_cast hnd
  push_cast [Nat.cast_sub (by omega : 2 ≤ q)]
  rw [cast_DDEN]
  field_simp

open MinModulus.CheckerSound.B in
/-- `h2Up` rounds up: `ν (q−1) 2^A / (q^A (q−2)) ≤ pv (h2Up q dn A)` (`q ≥ 3`). -/
theorem h2Up_ge {q dn : ℕ} (hq : 3 ≤ q) (h : dn < DDEN) (A : ℕ) :
    tiltN dn * ((q : ℝ) - 1) * 2 ^ A / ((q : ℝ) ^ A * ((q : ℝ) - 2)) ≤ pv (h2Up q dn A) := by
  have hnd := nuDen_pos h
  have hq2 : 0 < q - 2 := by omega
  unfold h2Up
  refine le_of_eq_of_le ?_ (pv_ratUp2 (Nat.mul_pos (Nat.mul_pos hnd (pow_pos (by omega) _)) hq2))
  rw [tiltN_eq_div_nuDen h]
  have hq2' : (0 : ℝ) < (q : ℝ) - 2 := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hq0 : (0 : ℝ) < q := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hnd0 : (0 : ℝ) < ((nuDen dn : ℕ) : ℝ) := by exact_mod_cast hnd
  push_cast [Nat.cast_sub (by omega : 2 ≤ q), Nat.cast_sub (by omega : 1 ≤ q)]
  rw [cast_DDEN]
  field_simp

/-! ### `idxSet` -/

theorem primes2_nodup (P : Params2) : (primes2 P).toList.Nodup :=
  MinModulus.CheckerSound.A.primesUpTo_nodup P.PX

theorem primes2_mem {P : Params2} {x : ℕ} (hx : x ∈ (primes2 P).toList) : x.Prime ∧ x ≤ P.PX :=
  MinModulus.CheckerSound.A.mem_primesUpTo.1 hx

theorem mem_take_drop {l : List ℕ} {lo n x : ℕ} :
    x ∈ (l.drop lo).take n ↔ ∃ i, lo ≤ i ∧ i < lo + n ∧ ∃ h : i < l.length, l[i] = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.length_take, List.length_drop] at hj
    refine ⟨lo + j, by omega, by omega, by omega, ?_⟩
    rw [List.getElem_take, List.getElem_drop]
  · rintro ⟨i, h1, h2, h3, rfl⟩
    refine ⟨i - lo, by rw [List.length_take, List.length_drop]; omega, ?_⟩
    rw [List.getElem_take, List.getElem_drop]
    congr 1
    omega

theorem aget_eq_list {xs : Array ℕ} {i : ℕ} (h : i < xs.toList.length) : xs[i]! = xs.toList[i] := by
  have h' : i < xs.size := by simpa using h
  rw [aget_def, Array.getElem?_eq_getElem h', Array.getElem_toList]
  rfl

/-- Membership in `idxSet`: `x ∈ idxSet P lo hi ↔ x = primes2 P [i]` for some `lo ≤ i < hi`. -/
theorem mem_idxSet {P : Params2} {lo hi x : ℕ} :
    x ∈ idxSet P lo hi ↔ ∃ i, lo ≤ i ∧ i < hi ∧ i < (primes2 P).size ∧ (primes2 P)[i]! = x := by
  unfold idxSet
  rw [List.mem_toFinset, mem_take_drop]
  constructor
  · rintro ⟨i, h1, h2, h3, rfl⟩
    refine ⟨i, h1, by omega, by simpa using h3, aget_eq_list h3⟩
  · rintro ⟨i, h1, h2, h3, rfl⟩
    have h3' : i < (primes2 P).toList.length := by simpa using h3
    refine ⟨i, h1, by omega, h3', (aget_eq_list h3').symm⟩

theorem idxSet_self (P : Params2) (lo : ℕ) : idxSet P lo lo = ∅ := by
  unfold idxSet
  simp

/-- The members of `idxSet` are primes `≤ PX`. -/
theorem idxSet_mem {P : Params2} {lo hi x : ℕ} (hx : x ∈ idxSet P lo hi) :
    x.Prime ∧ x ≤ P.PX := by
  obtain ⟨i, -, -, hi, rfl⟩ := mem_idxSet.1 hx
  have hi' : i < (primes2 P).toList.length := by simpa using hi
  rw [aget_eq_list hi']
  exact primes2_mem (List.getElem_mem hi')

/-- `primes2 P [i] = primes2 P [j]` iff `i = j` (in range; the primes are distinct). -/
theorem primes2_inj {P : Params2} {i j : ℕ} (hi : i < (primes2 P).size) (hj : j < (primes2 P).size)
    (h : (primes2 P)[i]! = (primes2 P)[j]!) : i = j := by
  have hi' : i < (primes2 P).toList.length := by simpa using hi
  have hj' : j < (primes2 P).toList.length := by simpa using hj
  rw [aget_eq_list hi', aget_eq_list hj'] at h
  exact ((primes2_nodup P).getElem_inj_iff).1 h

/-- An index outside `[lo, hi)` gives a prime outside `idxSet P lo hi`. -/
theorem getElem_notMem_idxSet {P : Params2} {lo hi i : ℕ} (hi' : i < (primes2 P).size)
    (h : ¬ (lo ≤ i ∧ i < hi)) : (primes2 P)[i]! ∉ idxSet P lo hi := by
  intro hm
  obtain ⟨j, h1, h2, h3, hj⟩ := mem_idxSet.1 hm
  have := primes2_inj h3 hi' hj
  subst this
  exact h ⟨h1, h2⟩

theorem idxSet_succ (P : Params2) {lo hi : ℕ} (hlh : lo ≤ hi) (hs : hi < (primes2 P).size) :
    idxSet P lo (hi + 1) = insert (primes2 P)[hi]! (idxSet P lo hi) := by
  ext x
  rw [mem_insert, mem_idxSet, mem_idxSet]
  constructor
  · rintro ⟨i, h1, h2, h3, rfl⟩
    by_cases hih : i = hi
    · subst hih; exact Or.inl rfl
    · exact Or.inr ⟨i, h1, by omega, h3, rfl⟩
  · rintro (rfl | ⟨i, h1, h2, h3, rfl⟩)
    · exact ⟨hi, hlh, by omega, hs, rfl⟩
    · exact ⟨i, h1, by omega, h3, rfl⟩

end MinModulus.Checker2Sound.C
