import MinModulus.CheckerImpl.Primes
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Intervals

/-!
# CheckerSound (CS-A): the prime sieve, `countUnmarked`, trial division and `primesUpTo`

STATUS: complete, no `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`).
`primesUpTo_toList` is the statement of `CheckerSound/Interfaces.lean` (same name).

Main results (namespace `MinModulus.CheckerSound.A`):
* `sieve_get_prime` : every prime `p` is unmarked in `sieve N` (`(sieve N).get! p = 0`);
* `countUnmarked_eq_card` : `countUnmarked c a b = #{i ∈ [a, b) | c.get! i = 0}`;
* `card_primes_le_countUnmarked` : `#{p ∈ [a, b) prime} ≤ countUnmarked (sieve N) a b`;
* `isPrimeTD_iff` : `isPrimeTD n = true ↔ n.Prime`;
* `primesUpTo_toList` : `(primesUpTo P).toList = (List.range (P + 1)).filter Nat.Prime`;
  `mem_primesUpTo`, `primesUpTo_sorted`.
-/

namespace MinModulus.CheckerSound.A

open MinModulus.CheckerImpl Finset

/-! ### ByteArray access -/

theorem get!_eq_data (c : ByteArray) (k : ℕ) : c.get! k = c.data[k]! := by
  cases c; rfl

theorem get!_push (c : ByteArray) (b : UInt8) (k : ℕ) :
    (c.push b).get! k = if k = c.size then b else c.get! k := by
  rw [get!_eq_data, get!_eq_data]
  have e : (c.push b).data = c.data.push b := by cases c; rfl
  rw [e]
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  have hs : c.size = c.data.size := rfl
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hs ▸ h1) h2
  · exact absurd (hs ▸ h2) h1
  · rfl

theorem get!_set!_ne (c : ByteArray) (j : ℕ) (v : UInt8) {k : ℕ} (hk : k ≠ j) :
    (c.set! j v).get! k = c.get! k := by
  rw [get!_eq_data, get!_eq_data]
  have e : (c.set! j v).data = c.data.set! j v := by cases c; rfl
  rw [e]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne (Ne.symm hk)]

/-! ### The sieve marks only composites -/

/-- The sieve invariant: every prime index is unmarked. -/
def PrimesUnmarked (c : ByteArray) : Prop := ∀ k, k.Prime → c.get! k = 0

theorem zeroBytes_go_get (n : ℕ) (b : ByteArray) (hb : ∀ k, b.get! k = 0) (k : ℕ) :
    (zeroBytes.go n b).get! k = 0 := by
  induction n generalizing b with
  | zero => exact hb k
  | succ n ih =>
    refine ih _ fun k => ?_
    rw [get!_push]
    split_ifs
    · rfl
    · exact hb k

theorem zeroBytes_get (n k : ℕ) : (zeroBytes n).get! k = 0 := by
  refine zeroBytes_go_get n _ (fun k => ?_) k
  rw [get!_eq_data]
  rfl

theorem markFrom_unmarked {c : ByteArray} (hc : PrimesUnmarked c) {i j : ℕ} (hi : 2 ≤ i)
    (hij : i ∣ j) (hlt : i < j) (N f : ℕ) : PrimesUnmarked (markFrom c i j N f) := by
  induction f generalizing c j with
  | zero => exact hc
  | succ f ih =>
    unfold markFrom
    split_ifs with hjN
    · refine ih (fun k hk => ?_) (dvd_add hij dvd_rfl) (by omega)
      have hkj : k ≠ j := by
        rintro rfl
        exact (Nat.not_prime_of_dvd_of_lt hij hi hlt) hk
      rw [get!_set!_ne _ _ _ hkj]
      exact hc k hk
    · exact hc

theorem sieveOuter_unmarked (N : ℕ) {c : ByteArray} (hc : PrimesUnmarked c) {i : ℕ}
    (hi : 2 ≤ i) (f : ℕ) : PrimesUnmarked (sieveOuter N c i f) := by
  induction f generalizing c i with
  | zero => exact hc
  | succ f ih =>
    rw [sieveOuter]
    by_cases hii : i * i ≤ N
    · simp only [hii, ↓reduceIte]
      refine ih ?_ (by omega)
      by_cases h0 : (c.get! i == 0) = true
      · simp only [h0, ↓reduceIte]
        exact markFrom_unmarked hc hi (dvd_mul_right i i)
          (lt_of_lt_of_le (by omega : i < 2 * i) (Nat.mul_le_mul_right i hi)) N (N + 1)
      · simp only [h0]
        exact hc
    · simp only [hii, ↓reduceIte]
      exact hc

/-- **Every prime is unmarked in the sieve.** -/
theorem sieve_get_prime (N : ℕ) {p : ℕ} (hp : p.Prime) : (sieve N).get! p = 0 :=
  sieveOuter_unmarked N (fun k _ => zeroBytes_get (N + 1) k) le_rfl (N + 1) p hp

/-! ### `countUnmarked` -/

theorem countUnmarked_go (c : ByteArray) (i f acc : ℕ) :
    countUnmarked.go c i f acc = acc + ∑ t ∈ range f, if c.get! (i + t) = 0 then 1 else 0 := by
  induction f generalizing i acc with
  | zero => simp [countUnmarked.go]
  | succ f ih =>
    rw [countUnmarked.go, ih, sum_range_succ']
    simp only [Nat.add_zero]
    have e : ∀ t, i + 1 + t = i + (t + 1) := fun t => by omega
    simp only [e]
    by_cases h : c.get! i = 0
    · simp [h]; omega
    · have : (c.get! i == 0) = false := by simpa using h
      simp [this, h]

theorem countUnmarked_eq_card (c : ByteArray) (a b : ℕ) :
    countUnmarked c a b = #((Ico a b).filter (fun k => c.get! k = 0)) := by
  rw [countUnmarked, countUnmarked_go, zero_add, card_filter, sum_Ico_eq_sum_range]

/-- **`countUnmarked` bounds the number of primes** of `[a, b)` (for the sieve). -/
theorem card_primes_le_countUnmarked (N a b : ℕ) :
    #((Ico a b).filter Nat.Prime) ≤ countUnmarked (sieve N) a b := by
  rw [countUnmarked_eq_card]
  exact card_le_card fun k hk => by
    rw [mem_filter] at hk ⊢
    exact ⟨hk.1, sieve_get_prime N hk.2⟩

/-! ### Trial division -/

theorem noDivisorFrom_spec {n d f : ℕ} (h : noDivisorFrom n d f = true) :
    ∀ e, d ≤ e → e < d + f → e * e ≤ n → ¬ e ∣ n := by
  induction f generalizing d with
  | zero => intro e h1 h2; omega
  | succ f ih =>
    intro e hde hef hen hdiv
    rw [noDivisorFrom] at h
    by_cases h1 : n < d * d
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [h1, ↓reduceIte] at h
      by_cases h2 : (n % d == 0) = true
      · simp [h2] at h
      · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        rcases Nat.eq_or_lt_of_le hde with rfl | hlt
        · exact h2 (by simpa using Nat.mod_eq_zero_of_dvd hdiv)
        · exact ih h e hlt (by omega) hen hdiv

theorem noDivisorFrom_of {n d f : ℕ} (h : ∀ e, d ≤ e → e * e ≤ n → ¬ e ∣ n) :
    noDivisorFrom n d f = true := by
  induction f generalizing d with
  | zero => rfl
  | succ f ih =>
    rw [noDivisorFrom]
    by_cases h1 : n < d * d
    · simp [h1]
    · have hnd : ¬ d ∣ n := h d le_rfl (by omega)
      have h2 : (n % d == 0) = false := by
        simpa using fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
      simp only [h1, h2, ↓reduceIte, Bool.false_eq_true]
      exact ih fun e he => h e (by omega)

/-- **Trial division is correct.** -/
theorem isPrimeTD_iff (n : ℕ) : isPrimeTD n = true ↔ n.Prime := by
  unfold isPrimeTD
  rw [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨h2, h⟩
    by_contra hnp
    have hn1 : n ≠ 1 := by omega
    have hmp := Nat.minFac_prime hn1
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < n) hnp
    have hle : n.minFac ≤ n := Nat.minFac_le (by omega)
    exact noDivisorFrom_spec h n.minFac hmp.two_le (by omega) (by rw [sq] at hsq; exact hsq)
      (Nat.minFac_dvd n)
  · intro hp
    refine ⟨hp.two_le, noDivisorFrom_of fun e he hen hdiv => ?_⟩
    rcases hp.eq_one_or_self_of_dvd e hdiv with h1 | h1
    · omega
    · rw [h1] at hen
      have h2 := hp.two_le
      have : n * 2 ≤ n * n := Nat.mul_le_mul_left n h2
      omega

theorem isPrimeTD_eq_decide (n : ℕ) : isPrimeTD n = decide n.Prime := by
  by_cases h : n.Prime
  · rw [decide_eq_true h]; exact (isPrimeTD_iff n).2 h
  · rw [decide_eq_false h]
    cases hn : isPrimeTD n
    · rfl
    · exact absurd ((isPrimeTD_iff n).1 hn) h

/-! ### `primesUpTo` -/

theorem primesUpTo_go_toList (n f : ℕ) (acc : Array ℕ) :
    (primesUpTo.go n f acc).toList =
      acc.toList ++ (List.range' n f).filter (fun k => decide k.Prime) := by
  induction f generalizing n acc with
  | zero => simp [primesUpTo.go]
  | succ f ih =>
    rw [primesUpTo.go, ih, List.range'_succ, List.filter_cons, isPrimeTD_eq_decide]
    by_cases h : n.Prime
    · simp [h]
    · simp [h]

theorem primesUpTo_toList' (P : ℕ) :
    (primesUpTo P).toList = (List.range' 2 (P - 1)).filter (fun k => decide k.Prime) := by
  rw [primesUpTo, primesUpTo_go_toList]
  simp

/-- **`primesUpTo P` is the increasing list of the primes `≤ P`.** -/
theorem primesUpTo_toList (P : ℕ) :
    (primesUpTo P).toList = (List.range (P + 1)).filter (fun k => decide k.Prime) := by
  rw [primesUpTo_toList']
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · rfl
  · have e : List.range (P + 1) = List.range' 0 2 ++ List.range' 2 (P - 1) := by
      rw [List.range_eq_range', List.range'_append]
      congr 1
      omega
    rw [e, List.filter_append]
    have : (List.range' 0 2).filter (fun k => decide k.Prime) = [] := by decide
    rw [this, List.nil_append]

theorem mem_primesUpTo {P n : ℕ} : n ∈ (primesUpTo P).toList ↔ n.Prime ∧ n ≤ P := by
  rw [primesUpTo_toList, List.mem_filter, List.mem_range, decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

theorem primesUpTo_pairwise (P : ℕ) : (primesUpTo P).toList.Pairwise (· < ·) := by
  rw [primesUpTo_toList]
  exact (List.pairwise_lt_range).filter _

theorem primesUpTo_nodup (P : ℕ) : (primesUpTo P).toList.Nodup :=
  (primesUpTo_pairwise P).imp ne_of_lt

theorem primesUpTo_toFinset (P : ℕ) : (primesUpTo P).toList.toFinset = Nat.primesLE P := by
  ext n
  rw [List.mem_toFinset, mem_primesUpTo, Nat.mem_primesLE]
  exact and_comm

end MinModulus.CheckerSound.A
