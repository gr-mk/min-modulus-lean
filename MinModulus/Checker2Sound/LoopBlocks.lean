import MinModulus.Checker2Sound.LoopBasic
import MinModulus.Checker2Sound.LoopStmts

/-!
# `Checker2Sound.LoopBlocks`: the block phase `blockLoop2` of `run2` (L2-E)

STATUS: complete (fully proved); axioms `propext`, `Classical.choice`, `Quot.sound`. The stage-2
statements it uses (`ELawValid_add`, `splitCost_sound`) come from the hypothesis
`hS2 : Stage2Stmts` (`LoopStmts.lean`). Owned by L2-E (namespace `MinModulus.Checker2Sound.E`).

## Structure
* `addUnmarked_spec`: `addUnmarked` adds the unmarked numbers `unm sv i (i + f)` of `[i, i + f)`
  to a valid e-law (`ELawValid_add`, δ-value `dC = deltaN2 P j` for each such `j`) and counts them.
* `blockStep2`, `blockRec2`: one iteration of `blockLoop2` (`blockLoop2_succ`).
* `Chain2 B L E`: `L` is a list of consecutive nonempty blocks `[start, stop)` from `B` to `E`
  (`Chain2.cover`, `Chain2.find?_eq`, `Chain2.sum_le`), as in the first proof's `CheckerSound.A`.
* `blockLoop2_spec`: the loop (with `sv = sieve X`, a frozen `τ_s` table `tb = freeze st` of a
  valid `τ_s` state for `S`, and the e-law valid for `L0 ∪ unm sv (PX + 1) B` at the block start
  `B`) produces a chain from `B` to `max B (X + 1)`, `etaC = Σ count·val`, `count ≥ #primes`
  (`CheckerSound.A.sieve_get_prime`), the per-prime bound `hingeLoss ≤ pv val` for every prime of
  every block (`splitCost_sound` at the block start `B`: `m ≤ PX < B`, δ constant beyond `PX`,
  `primesBelow p ⊆ S ∪ L0 ∪ unm sv (PX + 1) E`), and the `T` bound over the primes below the end
  (`tailFactor_le_fac2'` with `Q = B`, `CheckerMath.prod_primesBelow_le_mul_pow`, `pv_powUp`).
-/

namespace MinModulus.Checker2Sound.E

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath MinModulus.Main

/-! ## `addUnmarked` -/

/-- The unmarked numbers of `[a, b)`. -/
def unm (sv : ByteArray) (a b : ℕ) : Finset ℕ := (Ico a b).filter (fun i => sv.get! i = 0)

theorem unm_self (sv : ByteArray) (a : ℕ) : unm sv a a = ∅ := by simp [unm]

theorem unm_union (sv : ByteArray) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    unm sv a b ∪ unm sv b c = unm sv a c := by
  unfold unm
  rw [← filter_union, Ico_union_Ico_eq_Ico hab hbc]

theorem mem_unm {sv : ByteArray} {a b i : ℕ} : i ∈ unm sv a b ↔ (a ≤ i ∧ i < b) ∧ sv.get! i = 0 := by
  simp [unm]

theorem unm_succ_of_zero (sv : ByteArray) {i f : ℕ} (h : sv.get! i = 0) :
    unm sv i (i + (f + 1)) = insert i (unm sv (i + 1) (i + 1 + f)) := by
  ext j
  simp only [mem_unm, mem_insert]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨by omega, by omega⟩, h3⟩
  · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
    · exact ⟨⟨le_rfl, by omega⟩, h⟩
    · exact ⟨⟨by omega, by omega⟩, h3⟩

theorem unm_succ_of_ne (sv : ByteArray) {i f : ℕ} (h : ¬ sv.get! i = 0) :
    unm sv i (i + (f + 1)) = unm sv (i + 1) (i + 1 + f) := by
  ext j
  simp only [mem_unm]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact absurd h3 h
    · exact ⟨⟨by omega, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by omega, by omega⟩, h3⟩

/-- **`addUnmarked`** adds the unmarked numbers of `[i, i + f)` to a valid e-law and counts them. -/
theorem addUnmarked_spec (hS2 : Stage2Stmts) (P : Params2) (sv : ByteArray) (dC : ℕ) :
    ∀ (f : ℕ) (el : ELaw) (L : Finset ℕ) (cnt i : ℕ), ELawValid P el L → (∀ q ∈ L, q < i) →
      3 ≤ i → i + f ≤ P.X + 1 → (∀ j, i ≤ j → j < i + f → deltaN2 P j = dC) →
      ELawValid P (addUnmarked sv P.NN dC el cnt i f).1 (L ∪ unm sv i (i + f)) ∧
      (addUnmarked sv P.NN dC el cnt i f).2 = cnt + #(unm sv i (i + f))
  | 0, el, L, cnt, i, hel, _, _, _, _ => by
    refine ⟨by simpa [addUnmarked, unm_self] using hel, by simp [addUnmarked, unm_self]⟩
  | f + 1, el, L, cnt, i, hel, hLi, hi3, hif, hdC => by
    rw [addUnmarked]
    by_cases h0 : sv.get! i = 0
    · have hb : (sv.get! i == 0) = true := by simp [h0]
      simp only [hb, ↓reduceIte]
      have hel' := hS2.ELawValid_add P hel hi3 (by omega) (fun h => absurd (hLi i h) (lt_irrefl i))
      rw [hdC i le_rfl (by omega)] at hel'
      obtain ⟨h1, h2⟩ := addUnmarked_spec hS2 P sv dC f (el.add P.NN i dC) (insert i L) (cnt + 1)
        (i + 1) hel' (fun q hq => by
          rcases mem_insert.1 hq with rfl | hq
          · omega
          · have := hLi q hq; omega) (by omega) (by omega)
        (fun j hj1 hj2 => hdC j (by omega) (by omega))
      have hnot : i ∉ unm sv (i + 1) (i + 1 + f) := fun h => by
        have := (mem_unm.1 h).1.1; omega
      rw [unm_succ_of_zero sv h0]
      refine ⟨?_, ?_⟩
      · rw [union_insert, ← insert_union]; exact h1
      · rw [h2, card_insert_of_notMem hnot]; ring
    · have hb : (sv.get! i == 0) = false := by simpa using h0
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2⟩ := addUnmarked_spec hS2 P sv dC f el L cnt (i + 1) hel
        (fun q hq => by have := hLi q hq; omega) (by omega) (by omega)
        (fun j hj1 hj2 => hdC j (by omega) (by omega))
      rw [unm_succ_of_ne sv h0]
      exact ⟨h1, h2⟩

/-- Every prime of `[a, b)` is unmarked by the sieve. -/
theorem card_primes_le_unm (X a b : ℕ) :
    #((Ico a b).filter Nat.Prime) ≤ #(unm (sieve X) a b) :=
  card_le_card fun q hq => by
    rw [mem_filter] at hq
    exact mem_filter.2 ⟨hq.1, MinModulus.CheckerSound.A.sieve_get_prime X hq.2⟩

/-! ## One iteration of the block loop -/

/-- The end of the block starting at `B`. -/
def blockEnd2 (P : Params2) (B : ℕ) : ℕ := min (B + max 1 (B >>> P.blockShift)) (P.X + 1)

theorem blockEnd2_gt (P : Params2) {B : ℕ} (h : B ≤ P.X) : B < blockEnd2 P B := by
  unfold blockEnd2
  omega

theorem blockEnd2_le (P : Params2) (B : ℕ) : blockEnd2 P B ≤ P.X + 1 := by
  unfold blockEnd2
  omega

/-- The e-law and the count after adding the unmarked numbers of the block starting at `B`. -/
def addU (P : Params2) (sv : ByteArray) (dC : ℕ) (st : BlkSt2) (B : ℕ) : ELaw × ℕ :=
  addUnmarked sv P.NN dC st.el 0 B (blockEnd2 P B - B)

/-- The block record pushed at the block start `B`. -/
def blockRec2 (P : Params2) (sv : ByteArray) (tb : TauSTab) (dC : ℕ) (st : BlkSt2) (B : ℕ) :
    BlockRec2 :=
  ⟨B, blockEnd2 P B, (addU P sv dC st B).2, splitCost P.m P.NN B dC tb (addU P sv dC st B).1⟩

/-- The state after the block starting at `B`. -/
def blockStep2 (P : Params2) (sv : ByteArray) (tb : TauSTab) (dC : ℕ) (st : BlkSt2) (B : ℕ) :
    BlkSt2 :=
  { etaC := st.etaC + (blockRec2 P sv tb dC st B).count * (blockRec2 P sv tb dC st B).val,
    T := mulUp st.T (powUp (fac2 B dC) (addU P sv dC st B).2),
    el := (addU P sv dC st B).1,
    blocks := st.blocks.push (blockRec2 P sv tb dC st B) }

theorem blockLoop2_zero (P : Params2) (sv : ByteArray) (tb : TauSTab) (dC : ℕ) (st : BlkSt2)
    (B : ℕ) : blockLoop2 P sv tb dC st B 0 = st := by
  rw [blockLoop2]

theorem blockLoop2_succ_of_gt (P : Params2) (sv : ByteArray) (tb : TauSTab) (dC : ℕ)
    (st : BlkSt2) (B f : ℕ) (h : P.X < B) : blockLoop2 P sv tb dC st B (f + 1) = st := by
  rw [blockLoop2]
  simp only [h, ↓reduceIte]

theorem blockLoop2_succ (P : Params2) (sv : ByteArray) (tb : TauSTab) (dC : ℕ) (st : BlkSt2)
    (B f : ℕ) (h : B ≤ P.X) :
    blockLoop2 P sv tb dC st B (f + 1) =
      blockLoop2 P sv tb dC (blockStep2 P sv tb dC st B) (blockEnd2 P B) f := by
  rw [blockLoop2]
  simp only [show ¬ P.X < B by omega, ↓reduceIte]
  rfl

/-! ## Chains of blocks -/

/-- `Chain2 B L E`: the blocks of `L` are consecutive nonempty intervals `[start, stop)`, the
first starting at `B` and the last ending at `E`. -/
def Chain2 : ℕ → List BlockRec2 → ℕ → Prop
  | B, [], E => B = E
  | B, b :: L, E => b.start = B ∧ B < b.stop ∧ Chain2 b.stop L E

theorem Chain2.bounds : ∀ {L : List BlockRec2} {B E : ℕ}, Chain2 B L E →
    B ≤ E ∧ ∀ b ∈ L, B ≤ b.start ∧ b.start < b.stop ∧ b.stop ≤ E
  | [], B, E, h => ⟨le_of_eq h, by simp⟩
  | b :: L, B, E, h => by
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨hle, hL⟩ := Chain2.bounds h3
    refine ⟨by omega, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨le_of_eq h1.symm, by omega, hle⟩
    · have := hL c hc
      exact ⟨by omega, this.2.1, this.2.2⟩

/-- Every point of `[B, E)` lies in a block of the chain. -/
theorem Chain2.cover : ∀ {L : List BlockRec2} {B E : ℕ}, Chain2 B L E →
    ∀ p, B ≤ p → p < E → ∃ b ∈ L, b.start ≤ p ∧ p < b.stop
  | [], B, E, h => fun p h1 h2 => by
    have : B = E := h
    omega
  | b :: L, B, E, h => fun p h1 h2 => by
    obtain ⟨hs, hlt, hc⟩ := h
    by_cases hp : p < b.stop
    · exact ⟨b, List.mem_cons_self .., by omega, hp⟩
    · obtain ⟨c, hcL, hc1, hc2⟩ := Chain2.cover hc p (by omega) h2
      exact ⟨c, List.mem_cons_of_mem _ hcL, hc1, hc2⟩

/-- The blocks of a chain are disjoint: `find?` returns the block containing `p`. -/
theorem Chain2.find?_eq : ∀ {L : List BlockRec2} {B E : ℕ}, Chain2 B L E →
    ∀ b ∈ L, ∀ p, b.start ≤ p → p < b.stop →
      L.find? (fun c => decide (c.start ≤ p) && decide (p < c.stop)) = some b
  | [], _, _, _ => fun b hb => by simp at hb
  | b0 :: L, B, E, h => fun b hb p h1 h2 => by
    have hbounds := (Chain2.bounds h).2
    obtain ⟨hs, hlt, hc⟩ := h
    have hbL := (Chain2.bounds hc).2
    by_cases hp : p < b0.stop
    · have hb0 : b0.start ≤ p := by
        have := (hbounds b hb).1
        omega
      rw [List.find?_cons_of_pos (by simp [hb0, hp])]
      rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · have := (hbL b hb').1
        omega
    · rw [List.find?_cons_of_neg (by simp [hp])]
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd h2 hp
      · exact Chain2.find?_eq hc b hb' p h1 h2

/-- Sum over the primes of `[B, E)` of costs bounded blockwise. -/
theorem Chain2.sum_le (c : ℕ → ℝ) : ∀ {L : List BlockRec2} {B E : ℕ}, Chain2 B L E →
    (∀ b ∈ L, #((Ico b.start b.stop).filter Nat.Prime) ≤ b.count) →
    (∀ b ∈ L, ∀ p, p.Prime → b.start ≤ p → p < b.stop → c p ≤ pv b.val) →
    ∑ p ∈ (Ico B E).filter Nat.Prime, c p ≤ (L.map fun b => (b.count : ℝ) * pv b.val).sum
  | [], B, E, h => fun _ _ => by
    have : B = E := h
    subst this
    simp
  | b :: L, B, E, h => fun hcount hc => by
    obtain ⟨hs, hlt, hch⟩ := h
    have hle := (Chain2.bounds hch).1
    have hsplit : (Ico B E).filter Nat.Prime =
        (Ico B b.stop).filter Nat.Prime ∪ (Ico b.stop E).filter Nat.Prime := by
      rw [← filter_union, Ico_union_Ico_eq_Ico hlt.le hle]
    have hdisj : Disjoint ((Ico B b.stop).filter Nat.Prime) ((Ico b.stop E).filter Nat.Prime) :=
      disjoint_filter_filter (Ico_disjoint_Ico_consecutive B b.stop E)
    rw [hsplit, sum_union hdisj, List.map_cons, List.sum_cons]
    have h1 : ∑ p ∈ (Ico B b.stop).filter Nat.Prime, c p ≤ (b.count : ℝ) * pv b.val := by
      have hb := hc b (List.mem_cons_self ..)
      have hcnt : #((Ico B b.stop).filter Nat.Prime) ≤ b.count := by
        have := hcount b (List.mem_cons_self ..)
        rwa [hs] at this
      calc ∑ p ∈ (Ico B b.stop).filter Nat.Prime, c p
          ≤ #((Ico B b.stop).filter Nat.Prime) • pv b.val :=
            sum_le_card_nsmul _ _ _ fun p hp => by
              rw [mem_filter, mem_Ico] at hp
              exact hb p hp.2 (by omega) hp.1.2
        _ = (#((Ico B b.stop).filter Nat.Prime) : ℝ) * pv b.val := nsmul_eq_mul _ _
        _ ≤ (b.count : ℝ) * pv b.val :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) (pv_nonneg _)
    have h2 := Chain2.sum_le c hch (fun b' hb' => hcount b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => hc b' (List.mem_cons_of_mem _ hb'))
    linarith

theorem list_sum_pv (L : List BlockRec2) :
    (L.map fun b => (b.count : ℝ) * pv b.val).sum = pv ((L.map fun b => b.count * b.val).sum) := by
  induction L with
  | nil => simp [pv]
  | cons b L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, pv_add, pv_mul_nat]

/-- The per-prime cost of `p > PX` as `costOf2` reads it off the blocks. -/
def blockCost2 (blocks : Array BlockRec2) (p : ℕ) : ℕ :=
  match blocks.find? (fun b => b.start ≤ p && p < b.stop) with
  | some b => b.val
  | none => 0

/-- `blockCost2` reads the `val` of the block containing `p`. -/
theorem blockCost2_eq {blocks : Array BlockRec2} {B E : ℕ} (h : Chain2 B blocks.toList E)
    {b : BlockRec2} (hb : b ∈ blocks.toList) {p : ℕ} (h1 : b.start ≤ p) (h2 : p < b.stop) :
    blockCost2 blocks p = b.val := by
  unfold blockCost2
  rw [← Array.find?_toList, Chain2.find?_eq h b hb p h1 h2]

theorem costOf2_of_le (r : Result2) (P : Params2) {p : ℕ} (h : p ≤ P.PX) :
    costOf2 r P p = r.costs.getD p 0 := by
  unfold costOf2
  simp only [h, ↓reduceIte]

theorem costOf2_of_gt (r : Result2) (P : Params2) {p : ℕ} (h : P.PX < p) :
    costOf2 r P p = blockCost2 r.blocks p := by
  unfold costOf2 blockCost2
  simp only [show ¬ p ≤ P.PX by omega, ↓reduceIte]
  rfl

/-! ## The block loop -/

/-- The standing data of the block phase: the frozen `τ_s` table `tb = freeze tst` of a valid
`τ_s` state for `S`, the e-law's set `L0` of numbers `≤ PX` at the start (`S ∪ L0` covers the
primes `≤ PX`), the constant δ-value `dC` beyond `PX`, and the run-time guards. -/
structure BlockHyp2 (P : Params2) (tb : TauSTab) (dC : ℕ) (S L0 : Finset ℕ) : Prop where
  PX_le : P.PX ≤ P.X
  m_le : P.m ≤ P.PX
  m5 : 5 ≤ P.m
  dC_eq : ∀ p, P.PX < p → deltaN2 P p = dC
  tst : ∃ st : TauSState, TauSValid P st S ∧ tb = st.freeze P.TS
  S_le : ∀ q ∈ S, q ≤ P.PX
  L0_le : ∀ q ∈ L0, q ≤ P.PX
  disj : Disjoint S L0
  cover : Nat.primesLE P.PX ⊆ S ∪ L0

section Loop

variable (hS2 : Stage2Stmts) {P : Params2} {tb : TauSTab} {dC : ℕ} {S L0 : Finset ℕ}
  (hB : BlockHyp2 P tb dC S L0)
include hS2 hB

/-- The e-law after the block starting at `B` is valid for `L0 ∪ unm sv (PX + 1) E`. -/
theorem addU_valid {st : BlkSt2} {B : ℕ} (hPB : P.PX < B) (hBX : B ≤ P.X)
    (hel : ELawValid P st.el (L0 ∪ unm (sieve P.X) (P.PX + 1) B)) :
    ELawValid P (addU P (sieve P.X) dC st B).1 (L0 ∪ unm (sieve P.X) (P.PX + 1) (blockEnd2 P B)) ∧
      (addU P (sieve P.X) dC st B).2 = #(unm (sieve P.X) B (blockEnd2 P B)) := by
  have hBE := (blockEnd2_gt P hBX).le
  have hEX := blockEnd2_le P B
  obtain ⟨h1, h2⟩ := addUnmarked_spec hS2 P (sieve P.X) dC (blockEnd2 P B - B) st.el _ 0 B hel
    (fun q hq => by
      rcases mem_union.1 hq with hq | hq
      · have := hB.L0_le q hq; omega
      · exact (mem_unm.1 hq).1.2)
    (by have := hB.m5; have := hB.m_le; omega) (by omega)
    (fun j hj1 _ => hB.dC_eq j (by omega))
  rw [show B + (blockEnd2 P B - B) = blockEnd2 P B by omega] at h1 h2
  refine ⟨?_, by rw [addU, h2, zero_add]⟩
  rw [addU, union_assoc, unm_union _ (by omega) hBE] at *
  exact h1

/-- **The per-prime cost of a block** bounds the hinge loss of each of its primes. -/
theorem hinge_le_blockRec2 {st : BlkSt2} {B : ℕ} (hPB : P.PX < B) (hBX : B ≤ P.X)
    (hel : ELawValid P st.el (L0 ∪ unm (sieve P.X) (P.PX + 1) B)) {p : ℕ} (hp : p.Prime)
    (hBp : B ≤ p) (hpE : p < blockEnd2 P B) (N : ℕ) :
    hingeLoss P.m (delta2 P) p (fun _ => N) ≤
      pv (blockRec2 P (sieve P.X) tb dC st B).val := by
  obtain ⟨tst, hS, htb⟩ := hB.tst
  have hEX := blockEnd2_le P B
  have hpX : p ≤ P.X := by omega
  obtain ⟨hel', -⟩ := addU_valid hS2 hB hPB hBX hel
  have hdisj : Disjoint S (L0 ∪ unm (sieve P.X) (P.PX + 1) (blockEnd2 P B)) := by
    refine disjoint_union_right.2 ⟨hB.disj, disjoint_left.2 fun q hqS hqU => ?_⟩
    have h1 := hB.S_le q hqS
    have h2 := (mem_unm.1 hqU).1.1
    omega
  have hsub : Nat.primesBelow p ⊆ S ∪ (L0 ∪ unm (sieve P.X) (P.PX + 1) (blockEnd2 P B)) := by
    intro q hq
    obtain ⟨hqp, hqprime⟩ := Nat.mem_primesBelow.1 hq
    by_cases hqPX : q ≤ P.PX
    · rcases mem_union.1 (hB.cover (Nat.mem_primesLE.2 ⟨hqPX, hqprime⟩)) with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_union_left _ h)
    · exact mem_union_right _ (mem_union_right _ (mem_unm.2
        ⟨⟨by omega, by omega⟩, MinModulus.CheckerSound.A.sieve_get_prime P.X hqprime⟩))
  have hdnB : deltaN2 P B = dC := hB.dC_eq B hPB
  have hm := hB.m_le
  have h := hS2.splitCost_sound P hS hel' hdisj hp (by have := hB.m5; omega) hBp (Or.inr (by omega))
    hpX (by omega) hsub (by rw [hdnB, hB.dC_eq p (by omega)]) N
  rw [hdnB, ← htb] at h
  exact h

omit hS2 in
/-- One block preserves the `T` bound (over the primes below the block start). -/
theorem T_step {st : BlkSt2} {B : ℕ} (hPB : P.PX < B) (hBX : B ≤ P.X)
    (hT : ∏ q ∈ Nat.primesBelow B, tailFactor (delta2 P) q ≤ pv st.T) :
    ∏ q ∈ Nat.primesBelow (blockEnd2 P B), tailFactor (delta2 P) q ≤
      pv (mulUp st.T (powUp (fac2 B dC) #(unm (sieve P.X) B (blockEnd2 P B)))) := by
  have hBE := (blockEnd2_gt P hBX).le
  have hEX := blockEnd2_le P B
  have hB2 : 2 ≤ B := by have := hB.m5; have := hB.m_le; omega
  have hdnB : deltaN2 P B = dC := hB.dC_eq B hPB
  have hF1 : 1 ≤ pv (fac2 B dC) :=
    (one_le_tailFactor2 P (by omega : 1 ≤ B)).trans (tailFactor_le_fac2' hB2 le_rfl hBX hdnB)
  have hn : #((Nat.primesBelow (blockEnd2 P B)).filter (B ≤ ·)) ≤
      #(unm (sieve P.X) B (blockEnd2 P B)) := by
    refine le_trans (card_le_card fun q hq => ?_) (card_primes_le_unm P.X B (blockEnd2 P B))
    rw [mem_filter, Nat.mem_primesBelow] at hq
    exact mem_filter.2 ⟨mem_Ico.2 ⟨hq.2, hq.1.1⟩, hq.1.2⟩
  have h1 := prod_primesBelow_le_mul_pow hBE (tailFactor (delta2 P))
    (fun q hq => one_le_tailFactor2 P (Nat.prime_of_mem_primesBelow hq).one_lt.le)
    (F := pv (fac2 B dC)) (fun q hq hBq => tailFactor_le_fac2' hB2 hBq
      (by have := (Nat.mem_primesBelow.1 hq).1; omega) (hB.dC_eq q (by omega))) hn hF1
  refine h1.trans ?_
  refine pv_mulUp_le (prod_nonneg fun q hq =>
    tailFactor2_nonneg P (Nat.prime_of_mem_primesBelow hq).one_lt.le) (by positivity) hT ?_
  exact pv_powUp _ _

/-- **Specification of `blockLoop2`** (with the sieve of `X`, from a block start `B > PX` with
enough fuel). -/
theorem blockLoop2_spec :
    ∀ (f : ℕ) (st : BlkSt2) (B : ℕ), P.PX < B → P.X + 1 ≤ B + f →
      ELawValid P st.el (L0 ∪ unm (sieve P.X) (P.PX + 1) B) →
    ∃ L : List BlockRec2,
      (blockLoop2 P (sieve P.X) tb dC st B f).blocks.toList = st.blocks.toList ++ L ∧
      Chain2 B L (max B (P.X + 1)) ∧
      (blockLoop2 P (sieve P.X) tb dC st B f).etaC =
        st.etaC + (L.map fun b => b.count * b.val).sum ∧
      (∀ b ∈ L, #((Ico b.start b.stop).filter Nat.Prime) ≤ b.count) ∧
      (∀ b ∈ L, ∀ p, p.Prime → b.start ≤ p → p < b.stop → ∀ N : ℕ,
        hingeLoss P.m (delta2 P) p (fun _ => N) ≤ pv b.val) ∧
      (∏ q ∈ Nat.primesBelow B, tailFactor (delta2 P) q ≤ pv st.T →
        ∏ q ∈ Nat.primesBelow (max B (P.X + 1)), tailFactor (delta2 P) q ≤
          pv (blockLoop2 P (sieve P.X) tb dC st B f).T)
  | 0, st, B, _, hf, _ => by
    have hmax : max B (P.X + 1) = B := max_eq_left (by omega)
    refine ⟨[], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [blockLoop2_zero]; simp
    · rw [hmax]; rfl
    · rw [blockLoop2_zero]; simp
    · simp
    · simp
    · intro h
      rw [hmax, blockLoop2_zero]
      exact h
  | f + 1, st, B, hB', hf, hel => by
    by_cases hBX : P.X < B
    · have hmax : max B (P.X + 1) = B := max_eq_left (by omega)
      rw [blockLoop2_succ_of_gt _ _ _ _ _ _ _ hBX]
      refine ⟨[], by simp, by rw [hmax]; rfl, by simp, by simp, by simp, fun h => ?_⟩
      rw [hmax]
      exact h
    · have hBX' : B ≤ P.X := by omega
      have hBE := blockEnd2_gt P hBX'
      have hEX := blockEnd2_le P B
      have hmax : max B (P.X + 1) = max (blockEnd2 P B) (P.X + 1) := by
        rw [max_eq_right (by omega), max_eq_right hEX]
      obtain ⟨hel', hcnt⟩ := addU_valid hS2 hB hB' hBX' hel
      rw [blockLoop2_succ _ _ _ _ _ _ _ hBX']
      obtain ⟨L, hL1, hL2, hL3, hL4, hL5, hL6⟩ :=
        blockLoop2_spec f (blockStep2 P (sieve P.X) tb dC st B) (blockEnd2 P B) (by omega)
          (by omega) hel'
      refine ⟨blockRec2 P (sieve P.X) tb dC st B :: L, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hL1]
        simp [blockStep2, Array.toList_push, List.append_assoc]
      · rw [hmax]
        exact ⟨rfl, hBE, hL2⟩
      · rw [hL3]
        simp only [blockStep2, List.map_cons, List.sum_cons]
        ring
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · show #((Ico B (blockEnd2 P B)).filter Nat.Prime) ≤ (addU P (sieve P.X) dC st B).2
          rw [hcnt]
          exact card_primes_le_unm P.X B (blockEnd2 P B)
        · exact hL4 b hb'
      · intro b hb p hp h1 h2 N
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact hinge_le_blockRec2 hS2 hB hB' hBX' hel hp h1 h2 N
        · exact hL5 b hb' p hp h1 h2 N
      · intro hT
        rw [hmax]
        refine hL6 ?_
        have h := T_step hB hB' hBX' hT
        rw [← hcnt] at h
        exact h

end Loop

end MinModulus.Checker2Sound.E
