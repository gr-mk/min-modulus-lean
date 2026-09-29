import MinModulus.CheckerSound.Interfaces
import MinModulus.CheckerMath.ImplBridge

/-!
# `CheckerSound.Loop`: the prime loop of `run` (CS-D)

STATUS: complete, no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`. The CS-C
statement `ComparisonCostSound` (`comparisonCost_sound`, proved in `CompCost.lean`) is taken as
the hypothesis `hCC` (supplied in `Assembly.lean`); the other inputs come from `Interfaces.lean`
(CS-A, CS-B), all proved.

## Main result: `loop_sound`
For `P` with `PX ≤ X` and `KMAX ≥ 1`, after `primeLoop` over `primes = primesUpTo PX`
(`loopFinal P`, which is the prime loop of `run P`: `run_ok`, `run_costs`, `run_etaA`, …):
* `etaA + etaB = Σ_{p ≤ PX prime} costs[p]` (exact, in `ℕ`);
* `ETHyp P ET2 ET25 ET3`: the running products bound `Π_{q ≤ PX} fac_θ(q, dn_q)/2^62`;
* if `ok = true`: `hingeLoss P.m (delta0 P) p (fun _ => N) ≤ costs[p]/2^62` for every prime
  `p ≤ PX` and every cap `N`.

## The invariant `Inv P primes k st` (indices `< k` processed, `doneSet k = {primes[j] : j < k}`)
* `costs.size = PX + 1`; `etaA + etaB = Σ_{q ∈ doneSet k} costs[q]`;
* `Π_{q ∈ doneSet k} fac_θ(q)/2^62 ≤ ET_θ/2^62` (θ = 2, 5/2, 3; `mulUp` rounds up);
* `bLo ≤ bHi ≤ k`; `allZero → dn_j = 0` for `j < k`;
* `aValid → bLo = zIdx ∧ A = buildA primes[0:zIdx] dns[0:zIdx] KMAX`;
* `ok →` `BValid P B {primes[i] : bLo ≤ i < bHi}` (`idxSet`), and the cost bound for every
  `q ∈ doneSet k` (the flag `ok` never goes back to `true`, so it guards the semantic parts).

## The step (`stepPrime = finish ∘ core`, `stepPrime_eq` is `rfl`)
* `δ_p = 0` (`inv_step_zero`): `costs[p] = firstMoment P.m p primes[0:k]`; the guard
  `ok && allZero` gives `δ_q = 0` for all `q ≤ p`; `CheckerMath.hingeLoss_le_firstMoment_impl`.
* `δ_p > 0` (`inv_step_ne`): `nAz = numAPrimes … ≤ k`; `rebuild` (`rebuild_spec`: three cases,
  A re-built for the primes below `z = primes[nAz]`, B extended by `primes[nAz..bLo)` via
  `addToB_valid`), then `extendB` (`primes[bHi..k)`), so `B` is valid for the primes in `[z, p)`
  (`idxSet_eq`); `A` is valid by `buildA_valid`; then `ComparisonCostSound`.
* the final update (`inv_finish`): `costs[p] := cost`, `etaA`/`etaB` `+= cost`, `ET_θ` `*= fac_θ`.

## The array of primes (`primesUpTo_toList`: `primes.toList = primeList (PX + 1)`)
`get!_prime`, `get!_strictMono`, `get!_inj`, `exists_index`, `extract_toList`
(`primes[0:k] = the primes below primes[k]`), `doneSet_eq`, `doneSet_size`, `idxSet_eq`.
-/

namespace MinModulus.CheckerSound.D

open Finset MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Main MinModulus.CheckerSound

/-! ## The step of the prime loop, restated in small pieces -/

/-- The A/B re-split of `stepPrime` (when `z` changed). -/
def rebuild (P : Params) (primes dns : Array ℕ) (st : LoopSt) (nAz : ℕ) : LoopSt :=
  if st.aValid && nAz == st.zIdx then st
  else
    let bEmpty := st.bLo == st.bHi
    let okz := bEmpty || nAz ≤ st.bLo
    let (B, bLo, bHi) :=
      if bEmpty then (st.B, nAz, nAz)
      else (addToB primes dns st.B nAz (st.bLo - nAz), nAz, st.bHi)
    { st with B, bLo, bHi, ok := st.ok && okz, zIdx := nAz, aValid := true,
              A := buildA (primes.extract 0 nAz) (dns.extract 0 nAz) P.KMAX }

/-- The extension of the B part to the primes below `primes[k]`. -/
def extendB (primes dns : Array ℕ) (st : LoopSt) (k : ℕ) : LoopSt :=
  { st with B := addToB primes dns st.B st.bHi (k - st.bHi), bHi := k }

/-- `(cost, state)` computed by `stepPrime` before its final update. -/
def core (P : Params) (primes dns : Array ℕ) (st : LoopSt) (k : ℕ) : ℕ × LoopSt :=
  if dns[k]! == 0 then
    (firstMoment P.m primes[k]! (primes.extract 0 k), { st with ok := st.ok && st.allZero })
  else
    let nAz := numAPrimes primes k P.Z0 (cdiv P.m primes[k]!)
    let st := extendB primes dns (rebuild P primes dns st nAz) k
    let out := comparisonCost P primes[k]! dns[k]! (primes.extract 0 nAz) (dns.extract 0 nAz)
      st.A st.B
    (out.cost, { st with ok := st.ok && out.ok, nleaf := st.nleaf + out.nleaf })

/-- The final update of `stepPrime`. -/
def finish (P : Params) (p dn : ℕ) (cs : ℕ × LoopSt) : LoopSt :=
  { etaA := if p < P.PD then cs.2.etaA + cs.1 else cs.2.etaA
    etaB := if p < P.PD then cs.2.etaB else cs.2.etaB + cs.1
    ET2 := mulUp cs.2.ET2 (fac2 p dn)
    ET25 := mulUp cs.2.ET25 (fac25 p dn)
    ET3 := mulUp cs.2.ET3 (fac3 p dn)
    B := cs.2.B, bLo := cs.2.bLo, bHi := cs.2.bHi, A := cs.2.A, zIdx := cs.2.zIdx,
    aValid := cs.2.aValid, allZero := cs.2.allZero && dn == 0, ok := cs.2.ok,
    costs := cs.2.costs.set! p cs.1, nleaf := cs.2.nleaf }

theorem stepPrime_eq (P : Params) (primes dns : Array ℕ) (st : LoopSt) (k : ℕ) :
    stepPrime P primes dns st k = finish P primes[k]! dns[k]! (core P primes dns st k) := by
  rfl


/-! ## The sorted array of primes -/

/-- The increasing list of the primes below `M`. -/
abbrev primeList (M : ℕ) : List ℕ := (List.range M).filter (fun q => decide q.Prime)

theorem primeList_pairwise (M : ℕ) : (primeList M).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem primeList_nodup (M : ℕ) : (primeList M).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem mem_primeList {M q : ℕ} : q ∈ primeList M ↔ q.Prime ∧ q < M := by
  simp [primeList, List.mem_filter, List.mem_range, and_comm]

theorem primeList_toFinset (M : ℕ) : (primeList M).toFinset = Nat.primesBelow M := by
  ext q
  rw [List.mem_toFinset, mem_primeList, Nat.mem_primesBelow, and_comm]

/-- `primeList M = primeList c ++ c :: …` for a prime `c < M`. -/
theorem primeList_split {M c : ℕ} (hc : c.Prime) (hcM : c < M) :
    ∃ rest, primeList M = primeList c ++ c :: rest := by
  have e : M = c + ((M - c - 1) + 1) := by omega
  refine ⟨((List.range (M - c - 1)).map Nat.succ |>.map (c + ·)).filter
    (fun q => decide q.Prime), ?_⟩
  unfold primeList
  rw [e, List.range_add, List.filter_append, List.range_succ_eq_map, List.map_cons,
    List.filter_cons, ite_eq_left (by simpa using hc)]
  simp [List.map_map]

section PrimeArray

variable {M : ℕ} {primes : Array ℕ} (hL : primes.toList = primeList M)
include hL

theorem size_eq : primes.size = (primeList M).length := by
  rw [← Array.length_toList, hL]

theorem get!_eq {j : ℕ} (hj : j < primes.size) :
    primes[j]! = (primeList M)[j]'(by rw [← size_eq hL]; exact hj) := by
  rw [getElem!_pos primes j hj]
  simp only [← Array.getElem_toList, hL]

theorem get!_mem {j : ℕ} (hj : j < primes.size) : primes[j]! ∈ primeList M := by
  rw [get!_eq hL hj]
  exact List.getElem_mem _

theorem get!_prime {j : ℕ} (hj : j < primes.size) : (primes[j]!).Prime :=
  (mem_primeList.1 (get!_mem hL hj)).1

theorem get!_lt {j : ℕ} (hj : j < primes.size) : primes[j]! < M :=
  (mem_primeList.1 (get!_mem hL hj)).2

theorem get!_strictMono {i j : ℕ} (hij : i < j) (hj : j < primes.size) :
    primes[i]! < primes[j]! := by
  rw [get!_eq hL (hij.trans hj), get!_eq hL hj]
  exact List.pairwise_iff_getElem.1 (primeList_pairwise M) i j _ _ hij

theorem get!_mono {i j : ℕ} (hij : i ≤ j) (hj : j < primes.size) :
    primes[i]! ≤ primes[j]! := by
  rcases hij.lt_or_eq with h | rfl
  · exact (get!_strictMono hL h hj).le
  · exact le_rfl

theorem get!_lt_iff {i j : ℕ} (hi : i < primes.size) (hj : j < primes.size) :
    primes[i]! < primes[j]! ↔ i < j := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (get!_mono hL (not_lt.1 h') hi))
  · intro h
    exact get!_strictMono hL h hj

theorem get!_inj {i j : ℕ} (hi : i < primes.size) (hj : j < primes.size)
    (h : primes[i]! = primes[j]!) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · exact absurd h (get!_strictMono hL h' hj).ne
  · exact h'
  · exact absurd h (get!_strictMono hL h' hi).ne'

theorem exists_index {q : ℕ} (hq : q.Prime) (hqM : q < M) :
    ∃ j, j < primes.size ∧ primes[j]! = q := by
  have hmem : q ∈ primeList M := mem_primeList.2 ⟨hq, hqM⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hj' : j < primes.size := by rw [size_eq hL]; exact hj
  exact ⟨j, hj', get!_eq hL hj'⟩

/-- The first `k` entries are the primes below `primes[k]`. -/
theorem extract_toList {k : ℕ} (hk : k < primes.size) :
    (primes.extract 0 k).toList = primeList primes[k]! := by
  obtain ⟨rest, hrest⟩ := primeList_split (get!_prime hL hk) (get!_lt hL hk)
  have hlen : (primeList primes[k]!).length = k := by
    have hnd := primeList_nodup M
    have h1 : (primeList M)[(primeList primes[k]!).length]'(by
        rw [hrest, List.length_append, List.length_cons]; omega) = primes[k]! := by
      simp only [hrest]
      rw [List.getElem_append_right (le_refl _)]
      simp
    have h2 : (primeList M)[k]'(by rw [← size_eq hL]; exact hk) = primes[k]! :=
      (get!_eq hL hk).symm
    exact (List.Nodup.getElem_inj_iff hnd).1 (h1.trans h2.symm)
  rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, hL, hrest]
  exact List.take_left' hlen

/-! ### Index sets -/

theorem doneSet_eq {k : ℕ} (hk : k < primes.size) :
    (range k).image (fun j => primes[j]!) = Nat.primesBelow primes[k]! := by
  ext q
  simp only [mem_image, mem_range, Nat.mem_primesBelow]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨get!_strictMono hL hj hk, get!_prime hL (hj.trans hk)⟩
  · rintro ⟨hqk, hq⟩
    obtain ⟨j, hj, rfl⟩ := exists_index hL hq (hqk.trans (get!_lt hL hk))
    exact ⟨j, (get!_lt_iff hL hj hk).1 hqk, rfl⟩

theorem doneSet_size : (range primes.size).image (fun j => primes[j]!) = Nat.primesBelow M := by
  ext q
  simp only [mem_image, mem_range, Nat.mem_primesBelow]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨get!_lt hL hj, get!_prime hL hj⟩
  · rintro ⟨hqM, hq⟩
    obtain ⟨j, hj, rfl⟩ := exists_index hL hq hqM
    exact ⟨j, hj, rfl⟩

theorem not_mem_doneSet {k : ℕ} (hk : k < primes.size) :
    primes[k]! ∉ (range k).image (fun j => primes[j]!) := by
  simp only [mem_image, mem_range, not_exists, not_and]
  intro j hj h
  exact absurd (get!_inj hL (hj.trans hk) hk h) hj.ne

theorem idxSet_eq {a k : ℕ} (hak : a ≤ k) (hk : k < primes.size) :
    (Ico a k).image (fun j => primes[j]!) = (Nat.primesBelow primes[k]!).filter (primes[a]! ≤ ·) := by
  ext q
  simp only [mem_image, mem_Ico, mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨j, ⟨haj, hjk⟩, rfl⟩
    exact ⟨⟨get!_strictMono hL hjk hk, get!_prime hL (hjk.trans hk)⟩, get!_mono hL haj (hjk.trans hk)⟩
  · rintro ⟨⟨hqk, hq⟩, haq⟩
    obtain ⟨j, hj, rfl⟩ := exists_index hL hq (hqk.trans (get!_lt hL hk))
    refine ⟨j, ⟨?_, (get!_lt_iff hL hj hk).1 hqk⟩, rfl⟩
    by_contra h
    exact absurd haq (not_le.2 ((get!_lt_iff hL (by omega) (lt_of_le_of_lt hak hk)).2 (not_le.1 h)))

end PrimeArray

/-! ## The B part along the loop -/

/-- The primes with index in `[a, b)`. -/
def idxSet (primes : Array ℕ) (a b : ℕ) : Finset ℕ := (Ico a b).image (fun j => primes[j]!)

theorem idxSet_self (primes : Array ℕ) (a : ℕ) : idxSet primes a a = ∅ := by
  simp [idxSet]

theorem idxSet_union (primes : Array ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    idxSet primes a b ∪ idxSet primes b c = idxSet primes a c := by
  unfold idxSet
  rw [← image_union, Ico_union_Ico_eq_Ico hab hbc]

theorem idxSet_succ_left (primes : Array ℕ) {i n : ℕ} (h : i < n) :
    idxSet primes i n = insert primes[i]! (idxSet primes (i + 1) n) := by
  unfold idxSet
  rw [← image_insert]
  congr 1
  ext j
  simp only [mem_insert, mem_Ico]
  omega

theorem map_get! (primes : Array ℕ) (f : ℕ → ℕ) {i : ℕ} (hi : i < primes.size) :
    (primes.map f)[i]! = f primes[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos primes i hi, Array.getElem_map]

section AddToB

variable {M : ℕ} {primes : Array ℕ} (hL : primes.toList = primeList M)
include hL

/-- `addToB` adds the primes with index in `[i, i + f)` to a valid B-part state. -/
theorem addToB_valid (P : Params) (hM : M ≤ P.PMAX + 1) :
    ∀ (f i : ℕ) (B : BState) (T : Finset ℕ), BValid P B T → i + f ≤ primes.size →
      (∀ j, i ≤ j → j < i + f → primes[j]! ∉ T) →
      BValid P (addToB primes (primes.map (deltaN P)) B i f) (T ∪ idxSet primes i (i + f))
  | 0, i, B, T, hB, _, _ => by simpa [addToB, idxSet] using hB
  | f + 1, i, B, T, hB, hif, hdis => by
    have hi : i < primes.size := by omega
    have hB' : BValid P (B.addPrime primes[i]! (deltaN P primes[i]!)) (insert primes[i]! T) :=
      BValid_addPrime P hB (get!_prime hL hi) (by have := get!_lt hL hi; omega)
        (hdis i le_rfl (by omega))
    have ih := addToB_valid P hM f (i + 1) _ _ hB' (by omega) (fun j hj1 hj2 => by
      rw [mem_insert, not_or]
      refine ⟨fun h => ?_, hdis j (by omega) (by omega)⟩
      have := get!_inj hL (by omega) hi h
      omega)
    have e : insert primes[i]! T ∪ idxSet primes (i + 1) (i + 1 + f) =
        T ∪ idxSet primes i (i + (f + 1)) := by
      rw [idxSet_succ_left primes (show i < i + (f + 1) by omega),
        show i + (f + 1) = i + 1 + f by omega, insert_union, union_insert]
    rw [addToB, map_get! primes (deltaN P) hi, ← e]
    exact ih

end AddToB

/-! ## Equations for `rebuild` and `core` -/

theorem rebuild_of_valid (P : Params) (primes dns : Array ℕ) (st : LoopSt) (nAz : ℕ)
    (h : (st.aValid && nAz == st.zIdx) = true) : rebuild P primes dns st nAz = st := by
  unfold rebuild
  simp [h]

theorem rebuild_of_empty (P : Params) (primes dns : Array ℕ) (st : LoopSt) (nAz : ℕ)
    (h : (st.aValid && nAz == st.zIdx) = false) (he : st.bLo = st.bHi) :
    rebuild P primes dns st nAz =
      { st with
        bLo := nAz, bHi := nAz, zIdx := nAz, aValid := true,
        A := buildA (primes.extract 0 nAz) (dns.extract 0 nAz) P.KMAX } := by
  unfold rebuild
  simp [h, he]

theorem rebuild_of_ne (P : Params) (primes dns : Array ℕ) (st : LoopSt) (nAz : ℕ)
    (h : (st.aValid && nAz == st.zIdx) = false) (he : st.bLo ≠ st.bHi) :
    rebuild P primes dns st nAz =
      { st with
        B := addToB primes dns st.B nAz (st.bLo - nAz), bLo := nAz,
        ok := st.ok && decide (nAz ≤ st.bLo), zIdx := nAz, aValid := true,
        A := buildA (primes.extract 0 nAz) (dns.extract 0 nAz) P.KMAX } := by
  unfold rebuild
  have hb : (st.bLo == st.bHi) = (decide (st.bLo = st.bHi)) := rfl
  simp [h, he, hb]

theorem core_of_zero (P : Params) (primes dns : Array ℕ) (st : LoopSt) (k : ℕ)
    (h : dns[k]! = 0) :
    core P primes dns st k =
      (firstMoment P.m primes[k]! (primes.extract 0 k), { st with ok := st.ok && st.allZero }) := by
  unfold core
  simp [h]

theorem core_of_ne (P : Params) (primes dns : Array ℕ) (st : LoopSt) (k : ℕ)
    (h : dns[k]! ≠ 0) :
    core P primes dns st k =
      (let nAz := numAPrimes primes k P.Z0 (cdiv P.m primes[k]!)
       let st := extendB primes dns (rebuild P primes dns st nAz) k
       let out := comparisonCost P primes[k]! dns[k]! (primes.extract 0 nAz) (dns.extract 0 nAz)
         st.A st.B
       (out.cost, { st with ok := st.ok && out.ok, nleaf := st.nleaf + out.nleaf })) := by
  unfold core
  simp [h]

theorem numAPrimes_go_le (primes : Array ℕ) (Z0 M : ℕ) :
    ∀ (f j : ℕ), numAPrimes.go primes Z0 M j f ≤ j + f
  | 0, j => by simp [numAPrimes.go]
  | f + 1, j => by
    unfold numAPrimes.go
    dsimp only
    split_ifs
    · have := numAPrimes_go_le primes Z0 M f (j + 1)
      omega
    · omega

theorem numAPrimes_le (primes : Array ℕ) (k Z0 M : ℕ) : numAPrimes primes k Z0 M ≤ k := by
  have := numAPrimes_go_le primes Z0 M k 0
  unfold numAPrimes
  omega

/-! ## Arrays of costs -/

theorem getD_eq_get! (a : Array ℕ) (j : ℕ) : a.getD j 0 = a[j]! :=
  (Array.getElem!_eq_getD).symm

theorem getD_set!_self (a : Array ℕ) {i : ℕ} (v : ℕ) (h : i < a.size) :
    (a.set! i v).getD i 0 = v := by
  rw [getD_eq_get!, Array.getElem!_set!_self _ _ _ h]

theorem getD_set!_ne (a : Array ℕ) {i j : ℕ} (v : ℕ) (h : i ≠ j) :
    (a.set! i v).getD j 0 = a.getD j 0 := by
  rw [getD_eq_get!, getD_eq_get!, Array.getElem!_set!_ne _ _ _ _ h]

theorem pv_eq_div_ONE (x : ℕ) : pv x = (x : ℝ) / (ONE : ℕ) := by
  rw [pv, ONE_real]

/-! ## The invariant of the prime loop -/

/-- The set of the primes with index `< k`. -/
abbrev doneSet (primes : Array ℕ) (k : ℕ) : Finset ℕ := (range k).image (fun j => primes[j]!)

/-- **Invariant of `primeLoop`** after the indices `< k` have been processed. -/
structure Inv (P : Params) (primes : Array ℕ) (k : ℕ) (st : LoopSt) : Prop where
  size : st.costs.size = P.PX + 1
  eta : st.etaA + st.etaB = ∑ q ∈ doneSet primes k, st.costs.getD q 0
  e2 : ∏ q ∈ doneSet primes k, pv (fac2 q (deltaN P q)) ≤ pv st.ET2
  e25 : ∏ q ∈ doneSet primes k, pv (fac25 q (deltaN P q)) ≤ pv st.ET25
  e3 : ∏ q ∈ doneSet primes k, pv (fac3 q (deltaN P q)) ≤ pv st.ET3
  hi : st.bHi ≤ k
  lohi : st.bLo ≤ st.bHi
  zero : st.allZero = true → ∀ j < k, deltaN P primes[j]! = 0
  aval : st.aValid = true → st.bLo = st.zIdx ∧
    st.A = buildA (primes.extract 0 st.zIdx) ((primes.map (deltaN P)).extract 0 st.zIdx) P.KMAX
  bval : st.ok = true → BValid P st.B (idxSet primes st.bLo st.bHi)
  cost : st.ok = true → ∀ q ∈ doneSet primes k, ∀ N : ℕ,
    hingeLoss P.m (delta0 P) q (fun _ => N) ≤ pv (st.costs.getD q 0)

section Step

variable {P : Params} {primes : Array ℕ} (hL : primes.toList = primeList (P.PX + 1))
include hL

theorem prod_step {k : ℕ} (hk : k < primes.size) (g : ℕ → ℕ) (E : ℕ)
    (h : ∏ q ∈ doneSet primes k, pv (g q) ≤ pv E) :
    ∏ q ∈ doneSet primes (k + 1), pv (g q) ≤ pv (mulUp E (g primes[k]!)) := by
  rw [doneSet, range_add_one, image_insert, prod_insert (not_mem_doneSet hL hk)]
  calc pv (g primes[k]!) * ∏ q ∈ doneSet primes k, pv (g q)
      ≤ pv (g primes[k]!) * pv E := mul_le_mul_of_nonneg_left h (pv_nonneg _)
    _ = pv E * pv (g primes[k]!) := mul_comm _ _
    _ ≤ pv (mulUp E (g primes[k]!)) := pv_mul_le_mulUp _ _

/-- The final update of `stepPrime` preserves the invariant, given the facts about the
intermediate state `st3` and the cost of `p = primes[k]`. -/
theorem inv_finish {k : ℕ} (hk : k < primes.size) {st : LoopSt} (hinv : Inv P primes k st)
    (cost : ℕ) (st3 : LoopSt) (hA : st3.etaA = st.etaA) (hB : st3.etaB = st.etaB)
    (h2 : st3.ET2 = st.ET2) (h25 : st3.ET25 = st.ET25) (h3 : st3.ET3 = st.ET3)
    (hc : st3.costs = st.costs) (hz : st3.allZero = st.allZero) (hhi : st3.bHi ≤ k + 1)
    (hlohi : st3.bLo ≤ st3.bHi)
    (haval : st3.aValid = true → st3.bLo = st3.zIdx ∧
      st3.A = buildA (primes.extract 0 st3.zIdx) ((primes.map (deltaN P)).extract 0 st3.zIdx)
        P.KMAX)
    (hbval : st3.ok = true → BValid P st3.B (idxSet primes st3.bLo st3.bHi))
    (hok : st3.ok = true → st.ok = true)
    (hcost : st3.ok = true → ∀ N : ℕ,
      hingeLoss P.m (delta0 P) primes[k]! (fun _ => N) ≤ pv cost) :
    Inv P primes (k + 1) (finish P primes[k]! (deltaN P primes[k]!) (cost, st3)) := by
  have hpS := not_mem_doneSet hL hk
  have hpsize : primes[k]! < st.costs.size := by rw [hinv.size]; exact get!_lt hL hk
  have hne : ∀ q ∈ doneSet primes k, primes[k]! ≠ q := fun q hq h => hpS (h ▸ hq)
  have hS : doneSet primes (k + 1) = insert primes[k]! (doneSet primes k) := by
    rw [doneSet, range_add_one, image_insert]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [finish, hc, Array.size_set!, hinv.size]
  · simp only [finish, hc, hA, hB]
    rw [hS, sum_insert hpS, getD_set!_self _ _ hpsize,
      sum_congr rfl fun q hq => getD_set!_ne st.costs cost (hne q hq), ← hinv.eta]
    split_ifs <;> omega
  · simp only [finish, h2]
    exact prod_step hL hk (fun q => fac2 q (deltaN P q)) _ hinv.e2
  · simp only [finish, h25]
    exact prod_step hL hk (fun q => fac25 q (deltaN P q)) _ hinv.e25
  · simp only [finish, h3]
    exact prod_step hL hk (fun q => fac3 q (deltaN P q)) _ hinv.e3
  · exact hhi
  · exact hlohi
  · intro hzero j hj
    simp only [finish, hz, Bool.and_eq_true, beq_iff_eq] at hzero
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hinv.zero hzero.1 j hj
    · exact hzero.2
  · exact haval
  · exact hbval
  · intro hok' q hq N
    simp only [finish] at hok' ⊢
    rw [hS, mem_insert] at hq
    rcases hq with rfl | hq
    · rw [getD_set!_self _ _ (hc ▸ hpsize)]
      exact hcost hok' N
    · rw [getD_set!_ne _ _ (hne q hq), hc]
      exact hinv.cost (hok hok') q hq N

/-- The `δ = 0` step (first moment). -/
theorem inv_step_zero {k : ℕ} (hk : k < primes.size) (hPX : P.PX ≤ P.PMAX) {st : LoopSt}
    (hinv : Inv P primes k st) (h0 : deltaN P primes[k]! = 0) :
    Inv P primes (k + 1) (stepPrime P primes (primes.map (deltaN P)) st k) := by
  have hdn : (primes.map (deltaN P))[k]! = deltaN P primes[k]! := map_get! primes _ hk
  rw [stepPrime_eq, core_of_zero P primes _ st k (hdn.trans h0), hdn]
  refine inv_finish hL hk hinv _ _ rfl rfl rfl rfl rfl rfl rfl
    (Nat.le_succ_of_le hinv.hi) hinv.lohi hinv.aval ?_ ?_ ?_
  · intro hok
    simp only [Bool.and_eq_true] at hok
    exact hinv.bval hok.1
  · intro hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  · intro hok N
    simp only [Bool.and_eq_true] at hok
    have hp := get!_prime hL hk
    have hpX : primes[k]! ≤ P.PMAX := by have := get!_lt hL hk; omega
    have hδp : delta0 P primes[k]! = 0 := (delta0_eq_zero_iff hpX).2 h0
    have hδ : ∀ q ∈ Nat.primesBelow primes[k]!, delta0 P q = 0 := by
      intro q hq
      rw [← doneSet_eq hL hk] at hq
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hq
      rw [mem_range] at hj
      exact (delta0_eq_zero_iff (by have := get!_lt hL (hj.trans hk); omega)).2
        (hinv.zero hok.2 j hj)
    have hext := extract_toList hL hk
    rw [pv_eq_div_ONE]
    exact hingeLoss_le_firstMoment_impl (m := P.m) hp hδp hδ (primes.extract 0 k)
      (by rw [hext]; exact primeList_nodup _)
      (fun q => by rw [hext, mem_primeList, Nat.mem_primesBelow, and_comm]) (fun _ => N)

/-- What `rebuild` produces (the A part for the primes below `primes[nAz]`, the B part for the
primes with index in `[nAz, bHi)`). -/
theorem rebuild_spec {k : ℕ} (hk : k < primes.size) (hPX : P.PX ≤ P.PMAX) {st : LoopSt}
    (hinv : Inv P primes k st) {nAz : ℕ} (hnAz : nAz ≤ k) :
    let st1 := rebuild P primes (primes.map (deltaN P)) st nAz
    st1.etaA = st.etaA ∧ st1.etaB = st.etaB ∧ st1.ET2 = st.ET2 ∧ st1.ET25 = st.ET25 ∧
    st1.ET3 = st.ET3 ∧ st1.costs = st.costs ∧ st1.allZero = st.allZero ∧ st1.aValid = true ∧
    st1.zIdx = nAz ∧ st1.bLo = nAz ∧
    st1.A = buildA (primes.extract 0 nAz) ((primes.map (deltaN P)).extract 0 nAz) P.KMAX ∧
    st1.bHi ≤ k ∧
    (st1.ok = true → st.ok = true ∧ nAz ≤ st1.bHi ∧ BValid P st1.B (idxSet primes nAz st1.bHi)) := by
  intro st1
  by_cases hv : (st.aValid && nAz == st.zIdx) = true
  · have e : st1 = st := rebuild_of_valid P primes _ st nAz hv
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨hbz, hA⟩ := hinv.aval hv.1
    rw [e]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hv.1, hv.2.symm, hbz.trans hv.2.symm, ?_, hinv.hi,
      fun hok => ⟨hok, ?_, ?_⟩⟩
    · rw [hA, ← hv.2]
    · rw [hv.2, ← hbz]; exact hinv.lohi
    · rw [hv.2, ← hbz]; exact hinv.bval hok
  · rw [Bool.not_eq_true] at hv
    by_cases he : st.bLo = st.bHi
    · have e : st1 = _ := rebuild_of_empty P primes _ st nAz hv he
      rw [e]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnAz, fun hok => ⟨hok, le_rfl, ?_⟩⟩
      have hb := hinv.bval hok
      rw [he, idxSet_self] at hb
      rw [idxSet_self]
      exact hb
    · have e : st1 = _ := rebuild_of_ne P primes _ st nAz hv he
      rw [e]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hinv.hi, fun hok => ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨hok, hle⟩ := hok
      refine ⟨hok, hle.trans hinv.lohi, ?_⟩
      have hlo := hinv.lohi
      have hhi := hinv.hi
      have h := addToB_valid hL P (by omega) (st.bLo - nAz) nAz st.B _ (hinv.bval hok)
        (by omega) (fun j hj1 hj2 hmem => by
          obtain ⟨j', hj', hjj'⟩ := mem_image.1 hmem
          rw [mem_Ico] at hj'
          have := get!_inj hL (by omega) (by omega) hjj'
          omega)
      rw [show nAz + (st.bLo - nAz) = st.bLo by omega, union_comm,
        idxSet_union primes hle hlo] at h
      exact h

/-- `extendB` adds the primes with index in `[bHi, k)` to the B part. -/
theorem extendB_valid {k : ℕ} (hk : k < primes.size) (hPX : P.PX ≤ P.PMAX) {st1 : LoopSt}
    {nAz : ℕ} (h1 : nAz ≤ st1.bHi) (h2 : st1.bHi ≤ k)
    (hB : BValid P st1.B (idxSet primes nAz st1.bHi)) :
    BValid P (extendB primes (primes.map (deltaN P)) st1 k).B (idxSet primes nAz k) := by
  have h := addToB_valid hL P (by omega) (k - st1.bHi) st1.bHi st1.B _ hB (by omega)
    (fun j hj1 hj2 hmem => by
      obtain ⟨j', hj', hjj'⟩ := mem_image.1 hmem
      rw [mem_Ico] at hj'
      have := get!_inj hL (by omega) (by omega) hjj'
      omega)
  rw [show st1.bHi + (k - st1.bHi) = k by omega, idxSet_union primes h1 h2] at h
  exact h

/-- The `δ > 0` step (comparison bound). -/
theorem inv_step_ne (hCC : ComparisonCostSound) {k : ℕ} (hk : k < primes.size)
    (hPX : P.PX ≤ P.PMAX) (hK : 1 ≤ P.KMAX)
    {st : LoopSt} (hinv : Inv P primes k st) (h0 : deltaN P primes[k]! ≠ 0) :
    Inv P primes (k + 1) (stepPrime P primes (primes.map (deltaN P)) st k) := by
  have hdn : (primes.map (deltaN P))[k]! = deltaN P primes[k]! := map_get! primes _ hk
  rw [stepPrime_eq, core_of_ne P primes _ st k (hdn ▸ h0), hdn]
  dsimp only
  have hnAz := numAPrimes_le primes k P.Z0 (cdiv P.m primes[k]!)
  obtain ⟨hA, hB, h2, h25, h3, hc, hz, hav, hzI, hbL, hAe, hbH, hok1⟩ :=
    rebuild_spec hL hk hPX hinv hnAz
  refine inv_finish hL hk hinv _ _ hA hB h2 h25 h3 hc hz (by simp [extendB]) ?_ ?_ ?_ ?_ ?_
  · simp only [extendB, hbL]; exact hnAz
  · intro _
    simp only [extendB, hbL, hzI, hAe, and_self]
  · intro hok
    simp only [extendB, Bool.and_eq_true] at hok
    obtain ⟨-, h1, hBv⟩ := hok1 hok.1
    have hres := extendB_valid hL hk hPX h1 hbH hBv
    simp only [extendB] at hres ⊢
    rw [hbL]
    exact hres
  · intro hok
    simp only [extendB, Bool.and_eq_true] at hok
    exact (hok1 hok.1).1
  · intro hok N
    simp only [extendB, Bool.and_eq_true] at hok
    obtain ⟨-, h1, hBv⟩ := hok1 hok.1
    have hBv' := extendB_valid hL hk hPX h1 hbH hBv
    set nAz := numAPrimes primes k P.Z0 (cdiv P.m primes[k]!) with hnAzdef
    have hnk : nAz < primes.size := lt_of_le_of_lt hnAz hk
    have hp := get!_prime hL hk
    have hpX : primes[k]! ≤ P.PMAX := by have := get!_lt hL hk; omega
    have hext := extract_toList hL hnk
    have hAv := buildA_valid P hK (primes.extract 0 nAz) ((primes.map (deltaN P)).extract 0 nAz)
      (by rw [hext]; exact primeList_nodup _)
      (fun q hq => by
        rw [hext, mem_primeList] at hq
        exact ⟨hq.1, by have := get!_lt hL hnk; omega⟩)
      (by rw [Array.map_extract])
    rw [hext, primeList_toFinset] at hAv
    rw [idxSet, idxSet_eq hL hnAz hk] at hBv'
    have hAst : (extendB primes (primes.map (deltaN P))
        (rebuild P primes (primes.map (deltaN P)) st nAz) k).A =
        buildA (primes.extract 0 nAz) ((primes.map (deltaN P)).extract 0 nAz) P.KMAX := by
      simp only [extendB, hAe]
    rw [← hAst] at hAv
    exact hCC P hp hpX (Nat.pos_of_ne_zero h0) (get!_mono hL hnAz hk)
      (primes.extract 0 nAz) ((primes.map (deltaN P)).extract 0 nAz) hext
      (by rw [Array.map_extract]) hAv hBv' hok.2 N

/-- One step of the loop preserves the invariant. -/
theorem inv_step (hCC : ComparisonCostSound) {k : ℕ} (hk : k < primes.size)
    (hPX : P.PX ≤ P.PMAX) (hK : 1 ≤ P.KMAX) {st : LoopSt} (hinv : Inv P primes k st) :
    Inv P primes (k + 1) (stepPrime P primes (primes.map (deltaN P)) st k) := by
  by_cases h0 : deltaN P primes[k]! = 0
  · exact inv_step_zero hL hk hPX hinv h0
  · exact inv_step_ne hL hCC hk hPX hK hinv h0

/-- The loop preserves the invariant. -/
theorem inv_loop (hCC : ComparisonCostSound) (hPX : P.PX ≤ P.PMAX) (hK : 1 ≤ P.KMAX) :
    ∀ (f k : ℕ) (st : LoopSt), Inv P primes k st → k + f ≤ primes.size →
      Inv P primes (k + f) (primeLoop P primes (primes.map (deltaN P)) st k f)
  | 0, k, st, hinv, _ => by simpa [primeLoop] using hinv
  | f + 1, k, st, hinv, hkf => by
    rw [primeLoop, show k + (f + 1) = (k + 1) + f by omega]
    exact inv_loop hCC hPX hK f (k + 1) _ (inv_step hL hCC (by omega) hPX hK hinv) (by omega)

end Step

/-! ## `run`: the prime loop and the block phase -/

/-- The initial state of the prime loop in `run P`. -/
def loopInit (P : Params) : LoopSt :=
  { etaA := 0, etaB := 0, ET2 := ONE, ET25 := ONE, ET3 := ONE,
    B := BState.init
      ((primesUpTo P.PX).foldl (fun a p => max a ((deltaN P p) * (p - 1) / DDEN)) 0 + 4),
    bLo := 0, bHi := 0, A := ⟨#[], #[], ONE, 0, 0⟩, zIdx := 0, aValid := false,
    allZero := true, ok := true, costs := Array.replicate (P.PX + 1) 0, nleaf := 0 }

/-- The state after the prime loop of `run P`. -/
def loopFinal (P : Params) : LoopSt :=
  primeLoop P (primesUpTo P.PX) ((primesUpTo P.PX).map (deltaN P)) (loopInit P) 0
    (primesUpTo P.PX).size

theorem run_ok (P : Params) : (run P).ok = (loopFinal P).ok := rfl
theorem run_costs (P : Params) : (run P).costs = (loopFinal P).costs := rfl
theorem run_etaA (P : Params) : (run P).etaA = (loopFinal P).etaA := rfl
theorem run_etaB (P : Params) : (run P).etaB = (loopFinal P).etaB := rfl
theorem run_etaC (P : Params) :
    (run P).etaC = (blockPhase P (loopFinal P).ET2 (loopFinal P).ET25 (loopFinal P).ET3).etaC :=
  rfl
theorem run_T (P : Params) :
    (run P).T = (blockPhase P (loopFinal P).ET2 (loopFinal P).ET25 (loopFinal P).ET3).ET2 := rfl
theorem run_blocks (P : Params) :
    (run P).blocks =
      (blockPhase P (loopFinal P).ET2 (loopFinal P).ET25 (loopFinal P).ET3).blocks := rfl

theorem inv_init (P : Params) : Inv P (primesUpTo P.PX) 0 (loopInit P) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, le_rfl, le_rfl, ?_, ?_, ?_, ?_⟩
  · simp [loopInit]
  · simp [loopInit, doneSet]
  · simp [loopInit, doneSet, pv_ONE]
  · simp [loopInit, doneSet, pv_ONE]
  · simp [loopInit, doneSet, pv_ONE]
  · intro _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  · intro h
    simp [loopInit] at h
  · intro _
    simp only [loopInit, idxSet_self]
    exact BValid_init P (by omega)
  · intro _ q hq
    simp [doneSet] at hq

/-- **The prime loop of `run`** (`p ≤ PX`): `etaA + etaB = Σ_{p ≤ PX prime} costs[p]`; the
running moment products satisfy `ETHyp`; and, if the run-time guard `ok` holds, `costs[p]`
bounds the hinge loss of every prime `p ≤ PX`, for every uniform cap. -/
theorem loop_sound (hCC : ComparisonCostSound) (P : Params) (hPX : P.PX ≤ P.PMAX)
    (hK : 1 ≤ P.KMAX) :
    (loopFinal P).etaA + (loopFinal P).etaB =
        ∑ p ∈ Nat.primesLE P.PX, (loopFinal P).costs.getD p 0 ∧
      ETHyp P (loopFinal P).ET2 (loopFinal P).ET25 (loopFinal P).ET3 ∧
      ((loopFinal P).ok = true → ∀ p, p.Prime → p ≤ P.PX → ∀ N : ℕ,
        hingeLoss P.m (delta0 P) p (fun _ => N) ≤ pv ((loopFinal P).costs.getD p 0)) := by
  have hL : (primesUpTo P.PX).toList = primeList (P.PX + 1) := primesUpTo_toList P.PX
  have hinv := inv_loop hL hCC hPX hK (primesUpTo P.PX).size 0 (loopInit P) (inv_init P)
    (by omega)
  rw [Nat.zero_add] at hinv
  have hS : doneSet (primesUpTo P.PX) (primesUpTo P.PX).size = Nat.primesLE P.PX :=
    doneSet_size hL
  refine ⟨?_, ⟨?_, ?_, ?_⟩, fun hok p hp hpX N => ?_⟩
  · have h := hinv.eta; rw [hS] at h; exact h
  · have h := hinv.e2; rw [hS] at h; exact h
  · have h := hinv.e25; rw [hS] at h; exact h
  · have h := hinv.e3; rw [hS] at h; exact h
  · exact hinv.cost hok p (by rw [hS]; exact Nat.mem_primesLE.2 ⟨hpX, hp⟩) N

end MinModulus.CheckerSound.D
