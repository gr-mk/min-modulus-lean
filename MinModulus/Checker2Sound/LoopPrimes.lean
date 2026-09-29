import MinModulus.Checker2Sound.LoopBasic
import MinModulus.Checker2Sound.LoopStmts

/-!
# `Checker2Sound.LoopPrimes`: the prime loop `primeLoop2` of `run2` (L2-E)

STATUS: complete (fully proved); axioms `propext`, `Classical.choice`, `Quot.sound`. The stage-2
statements it uses (`HValid_init`, `HValid_extend`, `TauSValid_init`, `TauSValid_add`,
`ELawValid_init`, `ELawValid_add`, `sbhCost_sound`, `splitCost_sound`) are the hypothesis
`hS2 : Stage2Stmts` (`LoopStmts.lean`). Owned by L2-E (namespace `MinModulus.Checker2Sound.E`).

## Main result: `loop2_sound`
For `P` with `PX ≤ X` and the side conditions `1 ≤ KH`, `1 ≤ TS`, `5 ≤ m`, after
`primeLoop2` over `primes2 P = primesUpTo PX` (`loopFinal2 P`, the prime loop of `run2 P`):
* `etaA + etaB = Σ_{p ≤ PX prime} costs[p]` (exact);
* `∏_{q ≤ PX prime} tailFactor (delta2 P) q ≤ pv T`;
* the weighted `τ_s` state is valid for `sSet` (the primes `≤ PX` with `N1 = ⌈m/q⌉ ≥ 3`), the
  frozen table `tb` (if any) is its freeze, and the e-law is valid for `lSet` (those with
  `N1 ≤ 2`); `sSet ∪ lSet = primesLE PX`, disjoint;
* if `ok = true`: `hingeLoss P.m (delta2 P) p (fun _ => N) ≤ pv costs[p]` for every prime
  `p ≤ PX` and every cap `N`.

## The invariant `Inv P k st` (indices `< k` processed)
`costs.size = PX + 1`; `etaA + etaB = Σ_{doneSet k} costs`; the `T` bound over `doneSet k`;
`allZero → δ = 0` below `k`; `TauSValid` for `sSet P k`, `ELawValid` for `lSet P k` (both
unconditional); `tb = some t → t = freeze tauS ∧` some earlier prime has `N1 ≤ 2`; and, if `ok`,
`HValid P H` and the cost bounds over `doneSet k`.

## The step (`stepPrime2 = fin2 ∘ core2`, `stepPrime2_eq` is `rfl`)
* `δ_p = 0`: `CheckerMath.hingeLoss_le_firstMoment_impl` (guard `ok && allZero`);
* `N1 ≥ 3`: `HValid_extend` (or `H` unchanged when `iN1 ≥ k`), then `sbhCost_sound`;
* `N1 ≤ 2`: `tb = freeze tauS`, `splitCost_sound` with `S = sSet`, `L = lSet`, `B = p`;
* `fin2`: `T ← mulUp T (fac2 p dn)` (`tailFactor_le_fac2'`), `p` joins `τ_s` (`TauSValid_add`)
  or the e-law (`ELawValid_add`, `p ≥ 3` since `m ≤ 2p` and `m ≥ 5`).
-/

namespace MinModulus.Checker2Sound.E

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath MinModulus.Main

/-! ## The step of the prime loop, restated in two pieces -/

/-- The part of `stepPrime2` before the final update. -/
def core2 (P : Params2) (primes dns : Array Nat) (st : LoopSt2) (k : Nat) : LoopSt2 :=
  let p := primes[k]!
  let dn := dns[k]!
  let N1 := cdiv P.m p
  if dn == 0 then
    let cost := firstMoment P.m p (primes.extract 0 k)
    { st with etaA := st.etaA + cost, costs := st.costs.set! p cost,
              ok := st.ok && st.allZero }
  else if 3 ≤ N1 then
    let iN1 := min (countLt primes N1) k
    let (H, okH) := st.H.extend primes dns P.KH iN1 k
    let out := sbhCost P p dn primes dns k H
    { st with etaB := st.etaB + out.cost, costs := st.costs.set! p out.cost, H,
              ok := st.ok && okH && out.ok, nleaf := st.nleaf + out.nleaf,
              npat := st.npat + out.npat, nprof := st.nprof + out.nprof }
  else
    let tb := match st.tb with
      | some tb => tb
      | none => st.tauS.freeze P.TS
    let cost := splitCost P.m P.NN p dn tb st.el
    { st with etaB := st.etaB + cost, costs := st.costs.set! p cost, tb := some tb,
              ok := st.ok && decide (3 ≤ p) }

/-- The final update of `stepPrime2`. -/
def fin2 (P : Params2) (p dn : Nat) (st : LoopSt2) : LoopSt2 :=
  let T := mulUp st.T (fac2 p dn)
  if 3 ≤ cdiv P.m p then
    { st with T, tauS := st.tauS.add P.TS p dn, allZero := st.allZero && dn == 0 }
  else
    { st with T, el := st.el.add P.NN p dn, allZero := st.allZero && dn == 0 }

theorem stepPrime2_eq (P : Params2) (primes dns : Array Nat) (st : LoopSt2) (k : Nat) :
    stepPrime2 P primes dns st k = fin2 P primes[k]! dns[k]! (core2 P primes dns st k) := rfl

/-! ### Fields of `fin2` -/

section Fin2

variable (P : Params2) (p dn : ℕ) (c : LoopSt2)

theorem fin2_etaA : (fin2 P p dn c).etaA = c.etaA := by unfold fin2; split <;> rfl
theorem fin2_etaB : (fin2 P p dn c).etaB = c.etaB := by unfold fin2; split <;> rfl
theorem fin2_costs : (fin2 P p dn c).costs = c.costs := by unfold fin2; split <;> rfl
theorem fin2_ok : (fin2 P p dn c).ok = c.ok := by unfold fin2; split <;> rfl
theorem fin2_H : (fin2 P p dn c).H = c.H := by unfold fin2; split <;> rfl
theorem fin2_tb : (fin2 P p dn c).tb = c.tb := by unfold fin2; split <;> rfl
theorem fin2_T : (fin2 P p dn c).T = mulUp c.T (fac2 p dn) := by unfold fin2; split <;> rfl
theorem fin2_allZero : (fin2 P p dn c).allZero = (c.allZero && dn == 0) := by
  unfold fin2; split <;> rfl

theorem fin2_tauS : (fin2 P p dn c).tauS =
    if 3 ≤ cdiv P.m p then c.tauS.add P.TS p dn else c.tauS := by
  unfold fin2; split <;> rfl

theorem fin2_el : (fin2 P p dn c).el =
    if 3 ≤ cdiv P.m p then c.el else c.el.add P.NN p dn := by
  unfold fin2; split <;> rfl

end Fin2

/-! ### The three branches of `core2` -/

section Core2

variable (P : Params2) (primes dns : Array ℕ) (st : LoopSt2) (k : ℕ)

theorem core2_zero (h : dns[k]! = 0) :
    core2 P primes dns st k =
      { st with etaA := st.etaA + firstMoment P.m (primes[k]!) (primes.extract 0 k),
                costs := st.costs.set! (primes[k]!) (firstMoment P.m (primes[k]!) (primes.extract 0 k)),
                ok := st.ok && st.allZero } := by
  unfold core2
  simp [h]

/-- The `H` state used at the S/B/H prime `primes[k]`. -/
def extH (P : Params2) (primes dns : Array ℕ) (st : LoopSt2) (k : ℕ) : HState × Bool :=
  st.H.extend primes dns P.KH (min (countLt primes (cdiv P.m (primes[k]!))) k) k

theorem core2_sbh (h0 : ¬ dns[k]! = 0) (h3 : 3 ≤ cdiv P.m (primes[k]!)) :
    core2 P primes dns st k =
      { st with etaB := st.etaB + (sbhCost P (primes[k]!) (dns[k]!) primes dns k
                  (extH P primes dns st k).1).cost,
                costs := st.costs.set! (primes[k]!) (sbhCost P (primes[k]!) (dns[k]!) primes dns k
                  (extH P primes dns st k).1).cost,
                H := (extH P primes dns st k).1,
                ok := st.ok && (extH P primes dns st k).2 && (sbhCost P (primes[k]!) (dns[k]!)
                  primes dns k (extH P primes dns st k).1).ok,
                nleaf := st.nleaf + (sbhCost P (primes[k]!) (dns[k]!) primes dns k
                  (extH P primes dns st k).1).nleaf,
                npat := st.npat + (sbhCost P (primes[k]!) (dns[k]!) primes dns k
                  (extH P primes dns st k).1).npat,
                nprof := st.nprof + (sbhCost P (primes[k]!) (dns[k]!) primes dns k
                  (extH P primes dns st k).1).nprof } := by
  have h0' : (dns[k]! == 0) = false := by simpa using h0
  unfold core2 extH
  simp only [h0', h3, ↓reduceIte, Bool.false_eq_true]

theorem core2_split (h0 : ¬ dns[k]! = 0) (h3 : ¬ 3 ≤ cdiv P.m (primes[k]!)) :
    core2 P primes dns st k =
      { st with etaB := st.etaB + splitCost P.m P.NN (primes[k]!) (dns[k]!)
                  (st.tb.getD (st.tauS.freeze P.TS)) st.el,
                costs := st.costs.set! (primes[k]!) (splitCost P.m P.NN (primes[k]!) (dns[k]!)
                  (st.tb.getD (st.tauS.freeze P.TS)) st.el),
                tb := some (st.tb.getD (st.tauS.freeze P.TS)),
                ok := st.ok && decide (3 ≤ primes[k]!) } := by
  have h0' : (dns[k]! == 0) = false := by simpa using h0
  unfold core2
  simp only [h0', h3, ↓reduceIte, Bool.false_eq_true]
  cases st.tb <;> rfl

end Core2

theorem extend_of_ge (H : HState) (primes dns : Array ℕ) (KH iN1 k : ℕ) (h : k ≤ iN1) :
    H.extend primes dns KH iN1 k = (H, H.lo == H.hi) := by
  unfold HState.extend
  simp [h]

/-! ## Sets of processed primes -/

/-- The processed primes with `N1 = ⌈m/q⌉ ≥ 3` (they form the `τ_s` law). -/
def sSet (P : Params2) (k : ℕ) : Finset ℕ :=
  (MinModulus.CheckerSound.D.doneSet (primes2 P) k).filter (fun q => 3 ≤ cdiv P.m q)

/-- The processed primes with `N1 ≤ 2` (they form the e-law). -/
def lSet (P : Params2) (k : ℕ) : Finset ℕ :=
  (MinModulus.CheckerSound.D.doneSet (primes2 P) k).filter (fun q => ¬ 3 ≤ cdiv P.m q)

theorem sSet_union_lSet (P : Params2) (k : ℕ) :
    sSet P k ∪ lSet P k = MinModulus.CheckerSound.D.doneSet (primes2 P) k := by
  unfold sSet lSet
  exact filter_union_filter_not_eq _ _

theorem disjoint_sSet_lSet (P : Params2) (k : ℕ) : Disjoint (sSet P k) (lSet P k) :=
  disjoint_filter_filter_not _ _ _

theorem doneSet_succ (P : Params2) (k : ℕ) :
    MinModulus.CheckerSound.D.doneSet (primes2 P) (k + 1) =
      insert (primes2 P)[k]! (MinModulus.CheckerSound.D.doneSet (primes2 P) k) := by
  rw [MinModulus.CheckerSound.D.doneSet, range_add_one, image_insert]

theorem sSet_succ (P : Params2) (k : ℕ) :
    sSet P (k + 1) = if 3 ≤ cdiv P.m (primes2 P)[k]! then insert (primes2 P)[k]! (sSet P k)
      else sSet P k := by
  unfold sSet
  rw [doneSet_succ, filter_insert]

theorem lSet_succ (P : Params2) (k : ℕ) :
    lSet P (k + 1) = if 3 ≤ cdiv P.m (primes2 P)[k]! then lSet P k
      else insert (primes2 P)[k]! (lSet P k) := by
  unfold lSet
  rw [doneSet_succ, filter_insert]
  split_ifs <;> rfl

theorem mem_doneSet_le (P : Params2) {k q : ℕ}
    (hq : q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k) (hk : k ≤ (primes2 P).size) :
    q.Prime ∧ q ≤ P.PX := by
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hq
  rw [mem_range] at hj
  exact ⟨primes2_get!_prime P (by omega), primes2_get!_le P (by omega)⟩

/-! ## The invariant -/

/-- **Invariant of `primeLoop2`** after the indices `< k` have been processed. -/
structure Inv (P : Params2) (k : ℕ) (st : LoopSt2) : Prop where
  size : st.costs.size = P.PX + 1
  eta : st.etaA + st.etaB = ∑ q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k, st.costs.getD q 0
  T : ∏ q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k, tailFactor (delta2 P) q ≤ pv st.T
  zero : st.allZero = true → ∀ j < k, deltaN2 P (primes2 P)[j]! = 0
  tauS : TauSValid P st.tauS (sSet P k)
  el : ELawValid P st.el (lSet P k)
  tb : ∀ t, st.tb = some t → t = st.tauS.freeze P.TS ∧ ∃ j < k, cdiv P.m (primes2 P)[j]! ≤ 2
  H : st.ok = true → HValid P st.H
  cost : st.ok = true → ∀ q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k, ∀ N : ℕ,
    hingeLoss P.m (delta2 P) q (fun _ => N) ≤ pv (st.costs.getD q 0)

section Step

variable (hS2 : Stage2Stmts) {P : Params2} (hPX : P.PX ≤ P.X) (hm5 : 5 ≤ P.m)

include hm5 in
/-- A prime `p ≤ PX` with `N1 = ⌈m/p⌉ ≤ 2` is `≥ 3` (as `m ≥ 5`). -/
theorem three_le_of_cdiv_le_two {p : ℕ} (hp : p.Prime) (h : ¬ 3 ≤ cdiv P.m p) : 3 ≤ p := by
  have h2 : cdiv P.m p ≤ 2 := by omega
  rw [cdiv_le_two_iff hp.pos] at h2
  omega

include hS2 hPX hm5 in
/-- **The final update preserves the invariant**, given the facts about the intermediate state
`c = core2 …` and the cost of `p = primes[k]`. -/
theorem inv_fin {k : ℕ} (hk : k < (primes2 P).size) {st : LoopSt2} (hinv : Inv P k st)
    (c : LoopSt2) (cost : ℕ) (hT : c.T = st.T) (htauS : c.tauS = st.tauS) (hel : c.el = st.el)
    (hz : c.allZero = st.allZero) (hc : c.costs = st.costs.set! (primes2 P)[k]! cost)
    (heta : c.etaA + c.etaB = st.etaA + st.etaB + cost) (hok : c.ok = true → st.ok = true)
    (hH : c.ok = true → HValid P c.H)
    (hcost : c.ok = true → ∀ N : ℕ,
      hingeLoss P.m (delta2 P) (primes2 P)[k]! (fun _ => N) ≤ pv cost)
    (htb : ∀ t, c.tb = some t → t = st.tauS.freeze P.TS ∧
      ∃ j < k + 1, cdiv P.m (primes2 P)[j]! ≤ 2)
    (htb3 : 3 ≤ cdiv P.m (primes2 P)[k]! → c.tb = none) :
    Inv P (k + 1) (fin2 P (primes2 P)[k]! (deltaN2 P (primes2 P)[k]!) c) := by
  have hL := primes2_toList P
  set p := (primes2 P)[k]! with hpdef
  have hp : p.Prime := primes2_get!_prime P hk
  have hpPX : p ≤ P.PX := primes2_get!_le P hk
  have hpX : p ≤ P.X := hpPX.trans hPX
  have hpS := MinModulus.CheckerSound.D.not_mem_doneSet hL hk
  have hpsize : p < st.costs.size := by rw [hinv.size]; omega
  have hne : ∀ q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k, p ≠ q :=
    fun q hq h => hpS (by rw [← h] at hq; exact hq)
  have hS := doneSet_succ P k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- size
    rw [fin2_costs, hc, Array.size_set!, hinv.size]
  · -- eta
    rw [fin2_etaA, fin2_etaB, heta, fin2_costs, hc, hS, sum_insert hpS,
      MinModulus.CheckerSound.D.getD_set!_self _ _ hpsize,
      sum_congr rfl fun q hq => MinModulus.CheckerSound.D.getD_set!_ne st.costs cost (hne q hq),
      ← hinv.eta]
    ring
  · -- T
    rw [fin2_T, hT, hS, prod_insert hpS]
    have h1 := tailFactor_le_fac2' (P := P) hp.two_le le_rfl hpX rfl
    have h0 : 0 ≤ ∏ q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k, tailFactor (delta2 P) q :=
      prod_nonneg fun q hq => tailFactor2_nonneg P (mem_doneSet_le P hq hk.le).1.one_lt.le
    calc tailFactor (delta2 P) p * ∏ q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k,
          tailFactor (delta2 P) q
        = (∏ q ∈ MinModulus.CheckerSound.D.doneSet (primes2 P) k, tailFactor (delta2 P) q) *
            tailFactor (delta2 P) p := mul_comm _ _
      _ ≤ pv (mulUp st.T (fac2 p (deltaN2 P p))) :=
          pv_mulUp_le h0 (tailFactor2_nonneg P hp.one_lt.le) hinv.T h1
  · -- zero
    intro hzero j hj
    rw [fin2_allZero, hz, Bool.and_eq_true, beq_iff_eq] at hzero
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hinv.zero hzero.1 j hj
    · exact hzero.2
  · -- tauS
    rw [fin2_tauS, sSet_succ, htauS]
    split_ifs with h3
    · have hpS' : p ∉ sSet P k := fun h => hpS (mem_filter.1 h).1
      exact hS2.TauSValid_add P hinv.tauS hp hpX hpS'
    · exact hinv.tauS
  · -- el
    rw [fin2_el, lSet_succ, hel]
    split_ifs with h3
    · exact hinv.el
    · have hpL' : p ∉ lSet P k := fun h => hpS (mem_filter.1 h).1
      exact hS2.ELawValid_add P hinv.el (three_le_of_cdiv_le_two hm5 hp h3) hpX hpL'
  · -- tb
    intro t ht
    rw [fin2_tb] at ht
    obtain ⟨ht1, ht2⟩ := htb t ht
    refine ⟨?_, ht2⟩
    rw [fin2_tauS]
    split_ifs with h3
    · rw [htb3 h3] at ht
      exact absurd ht (by simp)
    · rw [htauS]; exact ht1
  · -- H
    intro hok'
    rw [fin2_ok] at hok'
    rw [fin2_H]
    exact hH hok'
  · -- cost
    intro hok' q hq N
    rw [fin2_ok] at hok'
    rw [fin2_costs, hc]
    rw [hS, mem_insert] at hq
    rcases hq with rfl | hq
    · rw [MinModulus.CheckerSound.D.getD_set!_self _ _ hpsize]
      exact hcost hok' N
    · rw [MinModulus.CheckerSound.D.getD_set!_ne _ _ (hne q hq)]
      exact hinv.cost (hok hok') q hq N

include hS2 hPX hm5 in
/-- The `δ = 0` step (first moment). -/
theorem inv_step_zero {k : ℕ} (hk : k < (primes2 P).size) {st : LoopSt2} (hinv : Inv P k st)
    (h0 : deltaN2 P (primes2 P)[k]! = 0) :
    Inv P (k + 1) (stepPrime2 P (primes2 P) (dns2 P) st k) := by
  have hL := primes2_toList P
  have hdn : (dns2 P)[k]! = deltaN2 P (primes2 P)[k]! := dns2_get! P hk
  rw [stepPrime2_eq, core2_zero P _ _ st k (hdn.trans h0), hdn]
  have hp := primes2_get!_prime P hk
  have hpX : (primes2 P)[k]! ≤ P.X := (primes2_get!_le P hk).trans hPX
  refine inv_fin hS2 hPX hm5 hk hinv _ (firstMoment P.m (primes2 P)[k]! ((primes2 P).extract 0 k))
    rfl rfl rfl rfl rfl (by simp only; ring) (fun h => ?_) (fun h => ?_) (fun h N => ?_)
    (fun t ht => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true] at h; exact h.1
  · simp only [Bool.and_eq_true] at h; exact hinv.H h.1
  · simp only [Bool.and_eq_true] at h
    have hδp : delta2 P (primes2 P)[k]! = 0 := (delta2_eq_zero_iff hpX).2 h0
    have hδ : ∀ q ∈ Nat.primesBelow (primes2 P)[k]!, delta2 P q = 0 := by
      intro q hq
      rw [← MinModulus.CheckerSound.D.doneSet_eq hL hk] at hq
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hq
      rw [mem_range] at hj
      exact (delta2_eq_zero_iff ((primes2_get!_le P (by omega)).trans hPX)).2
        (hinv.zero h.2 j hj)
    have hext := MinModulus.CheckerSound.D.extract_toList hL hk
    rw [pv_eq_div_ONE]
    exact hingeLoss_le_firstMoment_impl (m := P.m) hp hδp hδ ((primes2 P).extract 0 k)
      (by rw [hext]; exact MinModulus.CheckerSound.D.primeList_nodup _)
      (fun q => by
        rw [hext, MinModulus.CheckerSound.D.mem_primeList, Nat.mem_primesBelow, and_comm])
      (fun _ => N)
  · obtain ⟨h1, j, hj, hj2⟩ := hinv.tb t ht
    exact ⟨h1, j, by omega, hj2⟩
  · -- `tb` is unchanged; it is `none` when `N1 ≥ 3`
    rename_i h3
    cases htb : st.tb with
    | none => rfl
    | some t =>
      obtain ⟨-, j, hj, hj2⟩ := hinv.tb t htb
      exfalso
      have hpj : (primes2 P)[j]! ≤ (primes2 P)[k]! :=
        MinModulus.CheckerSound.D.get!_mono hL hj.le hk
      have hj' := (cdiv_le_two_iff (primes2_get!_prime P (by omega)).pos).1 hj2
      have hk' : cdiv P.m (primes2 P)[k]! ≤ 2 := (cdiv_le_two_iff hp.pos).2 (by omega)
      omega

include hS2 hPX hm5 in
/-- The S/B/H step (`δ > 0`, `N1 ≥ 3`). -/
theorem inv_step_sbh {k : ℕ} (hk : k < (primes2 P).size) {st : LoopSt2} (hinv : Inv P k st)
    (h0 : deltaN2 P (primes2 P)[k]! ≠ 0) (h3 : 3 ≤ cdiv P.m (primes2 P)[k]!) :
    Inv P (k + 1) (stepPrime2 P (primes2 P) (dns2 P) st k) := by
  have hL := primes2_toList P
  have hdn : (dns2 P)[k]! = deltaN2 P (primes2 P)[k]! := dns2_get! P hk
  rw [stepPrime2_eq, core2_sbh P _ _ st k (hdn ▸ h0) h3]
  -- the `H` state after `extend`
  have hHv : st.ok = true → (extH P (primes2 P) (dns2 P) st k).2 = true →
      HValid P (extH P (primes2 P) (dns2 P) st k).1 := by
    intro hok hokH
    unfold extH at hokH ⊢
    by_cases hlt : min (countLt (primes2 P) (cdiv P.m (primes2 P)[k]!)) k < k
    · exact (hS2.HValid_extend P hPX (hinv.H hok) hk.le hlt hokH).1
    · rw [extend_of_ge _ _ _ _ _ _ (by omega)]
      exact hinv.H hok
  rw [show fin2 P (primes2 P)[k]! (dns2 P)[k]! = fin2 P (primes2 P)[k]! (deltaN2 P (primes2 P)[k]!)
    from by rw [hdn]]
  refine inv_fin hS2 hPX hm5 hk hinv _ _ rfl rfl rfl rfl rfl (by simp only; ring) (fun h => ?_)
    (fun h => ?_) (fun h N => ?_) (fun t ht => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true] at h; exact h.1.1
  · simp only [Bool.and_eq_true] at h
    exact hHv h.1.1 h.1.2
  · simp only [Bool.and_eq_true] at h
    exact hS2.sbhCost_sound P hPX hk h3 (hHv h.1.1 h.1.2) h.2 N
  · obtain ⟨h1, j, hj, hj2⟩ := hinv.tb t ht
    exact ⟨h1, j, by omega, hj2⟩
  · cases htb : st.tb with
    | none => rfl
    | some t =>
      obtain ⟨-, j, hj, hj2⟩ := hinv.tb t htb
      exfalso
      have hp := primes2_get!_prime P hk
      have hpj : (primes2 P)[j]! ≤ (primes2 P)[k]! :=
        MinModulus.CheckerSound.D.get!_mono hL hj.le hk
      have hj' := (cdiv_le_two_iff (primes2_get!_prime P (by omega)).pos).1 hj2
      have hk' : cdiv P.m (primes2 P)[k]! ≤ 2 := (cdiv_le_two_iff hp.pos).2 (by omega)
      omega

include hS2 hPX hm5 in
/-- The τ-split step (`δ > 0`, `N1 ≤ 2`). -/
theorem inv_step_split {k : ℕ} (hk : k < (primes2 P).size) {st : LoopSt2} (hinv : Inv P k st)
    (h0 : deltaN2 P (primes2 P)[k]! ≠ 0) (h3 : ¬ 3 ≤ cdiv P.m (primes2 P)[k]!) :
    Inv P (k + 1) (stepPrime2 P (primes2 P) (dns2 P) st k) := by
  have hL := primes2_toList P
  have hdn : (dns2 P)[k]! = deltaN2 P (primes2 P)[k]! := dns2_get! P hk
  rw [stepPrime2_eq, core2_split P _ _ st k (hdn ▸ h0) h3]
  have hp := primes2_get!_prime P hk
  have hpX : (primes2 P)[k]! ≤ P.X := (primes2_get!_le P hk).trans hPX
  -- the frozen table is the freeze of the current `τ_s` state
  have htbe : st.tb.getD (st.tauS.freeze P.TS) = st.tauS.freeze P.TS := by
    cases htb : st.tb with
    | none => rfl
    | some t => exact (hinv.tb t htb).1
  rw [show fin2 P (primes2 P)[k]! (dns2 P)[k]! = fin2 P (primes2 P)[k]! (deltaN2 P (primes2 P)[k]!)
    from by rw [hdn]]
  refine inv_fin hS2 hPX hm5 hk hinv _ _ rfl rfl rfl rfl rfl (by simp only; ring) (fun h => ?_)
    (fun h => ?_) (fun h N => ?_) (fun t ht => ?_) (fun h => absurd h h3)
  · simp only [Bool.and_eq_true] at h; exact h.1
  · simp only [Bool.and_eq_true] at h; exact hinv.H h.1
  · rw [htbe, hdn]
    have hm : P.m ≤ 2 * (primes2 P)[k]! := (cdiv_le_two_iff hp.pos).1 (by omega)
    have hsub : Nat.primesBelow (primes2 P)[k]! ⊆ sSet P k ∪ lSet P k := by
      rw [sSet_union_lSet]
      exact (MinModulus.CheckerSound.D.doneSet_eq hL hk).superset
    exact hS2.splitCost_sound P hinv.tauS hinv.el (disjoint_sSet_lSet P k) hp hp.two_le le_rfl
      (Or.inl rfl) hpX hm hsub rfl N
  · simp only [Option.some.injEq] at ht
    rw [← ht, htbe]
    exact ⟨rfl, k, by omega, by omega⟩

include hS2 hPX hm5 in
/-- One step of the loop preserves the invariant. -/
theorem inv_step {k : ℕ} (hk : k < (primes2 P).size) {st : LoopSt2} (hinv : Inv P k st) :
    Inv P (k + 1) (stepPrime2 P (primes2 P) (dns2 P) st k) := by
  by_cases h0 : deltaN2 P (primes2 P)[k]! = 0
  · exact inv_step_zero hS2 hPX hm5 hk hinv h0
  · by_cases h3 : 3 ≤ cdiv P.m (primes2 P)[k]!
    · exact inv_step_sbh hS2 hPX hm5 hk hinv h0 h3
    · exact inv_step_split hS2 hPX hm5 hk hinv h0 h3

include hS2 hPX hm5 in
/-- The loop preserves the invariant. -/
theorem inv_loop : ∀ (f k : ℕ) (st : LoopSt2), Inv P k st → k + f ≤ (primes2 P).size →
    Inv P (k + f) (primeLoop2 P (primes2 P) (dns2 P) st k f)
  | 0, k, st, hinv, _ => by simpa [primeLoop2] using hinv
  | f + 1, k, st, hinv, hkf => by
    rw [primeLoop2, show k + (f + 1) = (k + 1) + f by omega]
    exact inv_loop f (k + 1) _ (inv_step hS2 hPX hm5 (by omega) hinv) (by omega)

end Step

/-! ## `run2`: the prime loop -/

/-- The initial state of the prime loop in `run2 P`. -/
def loopInit2 (P : Params2) : LoopSt2 :=
  { etaA := 0, etaB := 0, T := ONE, H := HState.init P.KH, tauS := TauSState.init P.TS,
    tb := none, el := ELaw.init P.NN, allZero := true, ok := true,
    costs := zeros (P.PX + 1), nleaf := 0, npat := 0, nprof := 0 }

/-- The state after the prime loop of `run2 P`. -/
def loopFinal2 (P : Params2) : LoopSt2 :=
  primeLoop2 P (primes2 P) (dns2 P) (loopInit2 P) 0 (primes2 P).size

theorem inv_init (hS2 : Stage2Stmts) {P : Params2} (hKH : 1 ≤ P.KH) (hTS : 1 ≤ P.TS) : Inv P 0 (loopInit2 P) := by
  have hs0 : sSet P 0 = ∅ := by simp [sSet]
  have hl0 : lSet P 0 = ∅ := by simp [lSet]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [loopInit2, zeros]
  · simp [loopInit2]
  · simp [loopInit2, pv_ONE]
  · intro _ j hj
    exact absurd hj (Nat.not_lt_zero j)
  · rw [hs0]; exact hS2.TauSValid_init P hTS
  · rw [hl0]; exact hS2.ELawValid_init P
  · intro t ht
    simp [loopInit2] at ht
  · intro _; exact hS2.HValid_init P hKH
  · intro _ q hq
    simp at hq

/-- **The prime loop of `run2`** (`p ≤ PX`). -/
theorem loop2_sound (hS2 : Stage2Stmts) {P : Params2} (hPX : P.PX ≤ P.X) (hm5 : 5 ≤ P.m) (hKH : 1 ≤ P.KH)
    (hTS : 1 ≤ P.TS) : Inv P (primes2 P).size (loopFinal2 P) := by
  have h := inv_loop hS2 hPX hm5 (primes2 P).size 0 (loopInit2 P) (inv_init hS2 hKH hTS) (by omega)
  rwa [Nat.zero_add] at h

theorem doneSet_final (P : Params2) :
    MinModulus.CheckerSound.D.doneSet (primes2 P) (primes2 P).size = Nat.primesLE P.PX :=
  MinModulus.CheckerSound.D.doneSet_size (primes2_toList P)

end MinModulus.Checker2Sound.E
