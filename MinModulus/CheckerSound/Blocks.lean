import MinModulus.CheckerSound.MomentCode
import MinModulus.CheckerSound.Sieve

/-!
# CheckerSound (CS-A): the block phase `blockLoop` (primes `PX < p ≤ X`)

STATUS: complete, no `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound`).

Statements of `CheckerSound/Interfaces.lean` proved here (same names, namespace
`MinModulus.CheckerSound.A`): `blockPhase_cost_sound`, `blockPhase_sum_le`, `blockPhase_T_le`.
Also `blockHyp_fullParams : BlockHyp fullParams 409200000` (δ = 0.4092 for `p ≥ 50000`).

## Structure
* `blockEnd`, `blockStep`: one iteration of `blockLoop` (`blockLoop_succ`).
* `Chain B L E`: `L` is a list of consecutive nonempty blocks `[start, stop)` from `B` to `E`
  (`Chain.cover`, `Chain.find?`: the blocks partition `[B, E)`, so `find?` returns the block
  containing `p`).
* `ETInv P B st`: the running products bound the products of the per-prime factors
  `tailFactor`, `fhFactor`, `cubeFactor` (of `delta0 P`) over the primes below `B`.
* `blockLoop_spec`: the loop produces a chain from `PX + 1` to `X + 1`, `etaC = Σ count·val`,
  `count ≥ #primes` (sieve), and, under `ETInv`, the per-prime bound `hingeLoss ≤ pv val` and
  `ETInv` at `X + 1`.
* The per-prime factors are `tailFactor` (θ = 2, also the factor of `T`), `fhFactor` (θ = 5/2,
  sup over the caps) and `cubeFactor` (θ = 3), see `MomentCode.lean`; `ETHyp` (the checker's
  per-prime values `fac_θ q dn_q` for `q ≤ PX`) implies `ETInv` at `PX + 1` (`blockPhase_spec`).
* Math layer: `CheckerMath.hingeLoss_le_blockVal`, `tailFactor_le_fac2`,
  `expect1_{sq,cube,five_halves}_le_fac*`, `prod_primesBelow_le_mul_pow` (ImplBridge / Glue).
-/

namespace MinModulus.CheckerSound.A

open MinModulus.CheckerImpl MinModulus.Smooth MinModulus.CheckerMath MinModulus.Main
  MinModulus.CheckerSound Finset

/-! ### One iteration of the loop -/

/-- The end of the block starting at `B`. -/
def blockEnd (P : Params) (B : ℕ) : ℕ := min (B + max 1 (B >>> P.blockShift)) (P.PMAX + 1)

/-- The state after processing the block starting at `B`. -/
def blockStep (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) : BlkSt :=
  let E := blockEnd P B
  let n := countUnmarked sv B E
  let dn := deltaN P B
  let ET2 := mulUp st.ET2 (powUp (fac2 B dn) n)
  let ET25 := mulUp st.ET25 (powUp (fac25 B dn) n)
  let ET3 := mulUp st.ET3 (powUp (fac3 B dn) n)
  let v := blockVal B dn ET2 ET25 ET3
  { etaC := st.etaC + n * v, ET2, ET25, ET3, blocks := st.blocks.push ⟨B, E, n, v⟩ }

theorem blockLoop_zero (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) :
    blockLoop P sv st B 0 = st := by
  rw [blockLoop]

theorem blockLoop_succ_of_gt (P : Params) (sv : ByteArray) (st : BlkSt) (B f : ℕ)
    (h : P.PMAX < B) : blockLoop P sv st B (f + 1) = st := by
  rw [blockLoop]
  simp only [h, ↓reduceIte]

theorem blockLoop_succ (P : Params) (sv : ByteArray) (st : BlkSt) (B f : ℕ) (h : B ≤ P.PMAX) :
    blockLoop P sv st B (f + 1) = blockLoop P sv (blockStep P sv st B) (blockEnd P B) f := by
  rw [blockLoop]
  simp only [show ¬ P.PMAX < B by omega, ↓reduceIte]
  rfl

theorem blockEnd_gt (P : Params) {B : ℕ} (h : B ≤ P.PMAX) : B < blockEnd P B := by
  unfold blockEnd
  omega

theorem blockEnd_le (P : Params) (B : ℕ) : blockEnd P B ≤ P.PMAX + 1 := by
  unfold blockEnd
  omega

/-! ### Chains of blocks -/

/-- `Chain B L E`: the blocks of `L` are consecutive nonempty intervals `[start, stop)`, the first
starting at `B` and the last ending at `E`. -/
def Chain : ℕ → List BlockRec → ℕ → Prop
  | B, [], E => B = E
  | B, b :: L, E => b.start = B ∧ B < b.stop ∧ Chain b.stop L E

theorem Chain.bounds : ∀ {L : List BlockRec} {B E : ℕ}, Chain B L E →
    B ≤ E ∧ ∀ b ∈ L, B ≤ b.start ∧ b.start < b.stop ∧ b.stop ≤ E
  | [], B, E, h => ⟨le_of_eq h, by simp⟩
  | b :: L, B, E, h => by
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨hle, hL⟩ := Chain.bounds h3
    refine ⟨by omega, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨le_of_eq h1.symm, by omega, hle⟩
    · have := hL c hc
      exact ⟨by omega, this.2.1, this.2.2⟩

/-- Every point of `[B, E)` lies in a block of the chain. -/
theorem Chain.cover : ∀ {L : List BlockRec} {B E : ℕ}, Chain B L E →
    ∀ p, B ≤ p → p < E → ∃ b ∈ L, b.start ≤ p ∧ p < b.stop
  | [], B, E, h => fun p h1 h2 => by
    have : B = E := h
    omega
  | b :: L, B, E, h => fun p h1 h2 => by
    obtain ⟨hs, hlt, hc⟩ := h
    by_cases hp : p < b.stop
    · exact ⟨b, List.mem_cons_self .., by omega, hp⟩
    · obtain ⟨c, hcL, hc1, hc2⟩ := Chain.cover hc p (by omega) h2
      exact ⟨c, List.mem_cons_of_mem _ hcL, hc1, hc2⟩

/-- The blocks of a chain are disjoint: `find?` returns the block containing `p`. -/
theorem Chain.find?_eq : ∀ {L : List BlockRec} {B E : ℕ}, Chain B L E →
    ∀ b ∈ L, ∀ p, b.start ≤ p → p < b.stop →
      L.find? (fun c => decide (c.start ≤ p) && decide (p < c.stop)) = some b
  | [], _, _, _ => fun b hb => by simp at hb
  | b0 :: L, B, E, h => fun b hb p h1 h2 => by
    have hbounds := (Chain.bounds h).2
    obtain ⟨hs, hlt, hc⟩ := h
    have hbL := (Chain.bounds hc).2
    by_cases hp : p < b0.stop
    · -- `p` is in the first block, which must be `b`
      have hb0 : b0.start ≤ p := by
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
      · exact Chain.find?_eq hc b hb' p h1 h2

/-- Sum over the primes of `[B, E)` of costs bounded blockwise. -/
theorem Chain.sum_le (c : ℕ → ℝ) : ∀ {L : List BlockRec} {B E : ℕ}, Chain B L E →
    (∀ b ∈ L, #((Ico b.start b.stop).filter Nat.Prime) ≤ b.count) →
    (∀ b ∈ L, ∀ p, p.Prime → b.start ≤ p → p < b.stop → c p ≤ pv b.val) →
    ∑ p ∈ (Ico B E).filter Nat.Prime, c p ≤ (L.map fun b => (b.count : ℝ) * pv b.val).sum
  | [], B, E, h => fun _ _ => by
    have : B = E := h
    subst this
    simp
  | b :: L, B, E, h => fun hcount hc => by
    obtain ⟨hs, hlt, hch⟩ := h
    have hle := (Chain.bounds hch).1
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
    have h2 := Chain.sum_le c hch (fun b' hb' => hcount b' (List.mem_cons_of_mem _ hb'))
      (fun b' hb' => hc b' (List.mem_cons_of_mem _ hb'))
    linarith

/-! ### `delta0` at primes, and on the blocks -/

theorem tilt_delta0_nonneg (P : Params) (q : ℕ) : 0 ≤ tilt (delta0 P) q :=
  tilt_nonneg (by linarith [delta0_le_half P q])

theorem tilt_delta0_le_self (P : Params) {q : ℕ} (hq : q.Prime) : tilt (delta0 P) q ≤ q :=
  tilt_le_self (delta0_le_half P q) hq

theorem delta0_le_one (P : Params) (q : ℕ) : delta0 P q ≤ 1 := by
  linarith [delta0_le_half P q]

theorem one_le_tailFactor0 (P : Params) {q : ℕ} (hq : q.Prime) : 1 ≤ tailFactor (delta0 P) q :=
  one_le_tailFactor (delta0_nonneg P q) (delta0_le_half P q) hq.one_lt.le

theorem one_le_fhFactor0 (P : Params) {q : ℕ} (hq : q.Prime) : 1 ≤ fhFactor (delta0 P) q :=
  one_le_fhFactor hq.one_lt (tilt_delta0_nonneg P q) (tilt_delta0_le_self P hq)

theorem one_le_cubeFactor0 (P : Params) {q : ℕ} (hq : q.Prime) : 1 ≤ cubeFactor (delta0 P) q :=
  one_le_cubeFactor hq.one_lt.le (tilt_delta0_nonneg P q)

/-- On the blocks, every prime has the tilt of the block start. -/
theorem tilt_block {P : Params} {dC : ℕ} (hP : BlockHyp P dC) {B q : ℕ} (hB : P.PX < B)
    (hBq : B ≤ q) (hq : q ≤ P.PMAX) :
    tilt (delta0 P) q = (DDEN : ℝ) / ((DDEN : ℝ) - deltaN P B) := by
  rw [tilt_delta0_eq hq, hP.const q (by omega) hq, hP.const B hB (by omega)]

theorem primesBelow_filter_ge_eq (B E : ℕ) :
    (Nat.primesBelow E).filter (B ≤ ·) = (Ico B E).filter Nat.Prime := by
  ext q
  simp only [mem_filter, Nat.mem_primesBelow, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, h1⟩

/-! ### The running products -/

/-- The invariant of the running products at the block start `B`: they bound the products of
the per-prime moment factors over the primes below `B`. -/
structure ETInv (P : Params) (B : ℕ) (st : BlkSt) : Prop where
  two : ∏ q ∈ Nat.primesBelow B, tailFactor (delta0 P) q ≤ pv st.ET2
  five_halves : ∏ q ∈ Nat.primesBelow B, fhFactor (delta0 P) q ≤ pv st.ET25
  three : ∏ q ∈ Nat.primesBelow B, cubeFactor (delta0 P) q ≤ pv st.ET3

/-- The block record pushed by `blockStep`. -/
def blockRecAt (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) : BlockRec :=
  ⟨B, blockEnd P B, countUnmarked sv B (blockEnd P B),
    blockVal B (deltaN P B) (blockStep P sv st B).ET2 (blockStep P sv st B).ET25
      (blockStep P sv st B).ET3⟩

theorem blockStep_blocks (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) :
    (blockStep P sv st B).blocks = st.blocks.push (blockRecAt P sv st B) := rfl

theorem blockStep_etaC (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) :
    (blockStep P sv st B).etaC =
      st.etaC + (blockRecAt P sv st B).count * (blockRecAt P sv st B).val := rfl

theorem blockStep_ET2 (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) :
    (blockStep P sv st B).ET2 =
      mulUp st.ET2 (powUp (fac2 B (deltaN P B)) (countUnmarked sv B (blockEnd P B))) := rfl

theorem blockStep_ET25 (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) :
    (blockStep P sv st B).ET25 =
      mulUp st.ET25 (powUp (fac25 B (deltaN P B)) (countUnmarked sv B (blockEnd P B))) := rfl

theorem blockStep_ET3 (P : Params) (sv : ByteArray) (st : BlkSt) (B : ℕ) :
    (blockStep P sv st B).ET3 =
      mulUp st.ET3 (powUp (fac3 B (deltaN P B)) (countUnmarked sv B (blockEnd P B))) := rfl

/-- One block multiplies the running product by `F^n`, `F ≥ 1` bounding every factor of the block. -/
theorem prod_step {B E n : ℕ} (hBE : B ≤ E) (f : ℕ → ℝ) (hf1 : ∀ q, q.Prime → 1 ≤ f q)
    {F : ℕ} (hF : ∀ q ∈ Nat.primesBelow E, B ≤ q → f q ≤ pv F) (hF1 : 1 ≤ pv F)
    (hn : #((Ico B E).filter Nat.Prime) ≤ n) {x : ℕ}
    (hx : ∏ q ∈ Nat.primesBelow B, f q ≤ pv x) :
    ∏ q ∈ Nat.primesBelow E, f q ≤ pv (mulUp x (powUp F n)) := by
  have hn' : #((Nat.primesBelow E).filter (B ≤ ·)) ≤ n := by
    rw [primesBelow_filter_ge_eq]; exact hn
  have h1 := prod_primesBelow_le_mul_pow hBE f
    (fun q hq => hf1 q (Nat.prime_of_mem_primesBelow hq)) hF hn' hF1
  refine h1.trans ?_
  refine pv_mulUp_le (prod_nonneg fun q hq =>
    zero_le_one.trans (hf1 q (Nat.prime_of_mem_primesBelow hq))) (by positivity) hx ?_
  exact pv_powUp F n

theorem one_le_of_expect1_le {q : ℕ} {ν : ℝ} {g : ℕ → ℝ} (hg : g 0 = 1) {x : ℝ}
    (h : expect1 q ν 0 g ≤ x) : 1 ≤ x := by
  rwa [expect1_zero_cap, hg] at h

/-- **One block preserves the running-product invariant.** -/
theorem ETInv_step (P : Params) {dC : ℕ} (hP : BlockHyp P dC) {st : BlkSt} {B : ℕ}
    (hB : P.PX < B) (hBX : B ≤ P.PMAX) (h : ETInv P B st) :
    ETInv P (blockEnd P B) (blockStep P (sieve P.PMAX) st B) := by
  have hBE := (blockEnd_gt P hBX).le
  have hEX := blockEnd_le P B
  have hB2 : 2 ≤ B := by have := hP.one_le_PX; omega
  have hdn : deltaN P B < DDEN := deltaN_lt_DDEN P B
  have hdn45 : deltaN P B ≤ 450000000 := deltaN_le P B
  have hν0 := nu_nonneg hdn
  have hn := card_primes_le_countUnmarked P.PMAX B (blockEnd P B)
  -- every prime of the block has the tilt of the block start
  have htilt : ∀ q ∈ Nat.primesBelow (blockEnd P B), B ≤ q →
      tilt (delta0 P) q = (DDEN : ℝ) / ((DDEN : ℝ) - deltaN P B) := fun q hq hBq =>
    tilt_block hP hB hBq (by have := (Nat.mem_primesBelow.1 hq).1; omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [blockStep_ET2]
    refine prod_step hBE _ (fun q hq => one_le_tailFactor0 P hq) (fun q hq hBq => ?_) ?_ hn h.two
    · rw [pv_eq_div_ONE]
      exact tailFactor_le_fac2 hB2 hBq hdn (delta0_le_one P q) (le_of_eq (htilt q hq hBq))
    · rw [pv_eq_div_ONE]
      exact one_le_of_expect1_le (by simp) (expect1_sq_le_fac2 hB2 le_rfl hdn hν0 le_rfl 0)
  · rw [blockStep_ET25]
    refine prod_step hBE _ (fun q hq => one_le_fhFactor0 P hq) (fun q hq hBq => ?_) ?_ hn
      h.five_halves
    · exact fhFactor_le_fac25 hB2 hBq hdn45 (tilt_delta0_nonneg P q) (le_of_eq (htilt q hq hBq))
    · rw [pv_eq_div_ONE]
      exact one_le_of_expect1_le (by simp) (expect1_five_halves_le_fac25 hB2 le_rfl hdn
        ((nu_le_two hdn45).trans (by exact_mod_cast hB2)) hν0 le_rfl 0)
  · rw [blockStep_ET3]
    refine prod_step hBE _ (fun q hq => one_le_cubeFactor0 P hq) (fun q hq hBq => ?_) ?_ hn h.three
    · exact cubeFactor_le_fac3 hB2 hBq hdn (tilt_delta0_nonneg P q) (le_of_eq (htilt q hq hBq))
    · rw [pv_eq_div_ONE]
      exact one_le_of_expect1_le (by simp) (expect1_cube_le_fac3 hB2 le_rfl hdn hν0 le_rfl 0)

/-- **The per-prime cost of a block** bounds the hinge loss of each of its primes. -/
theorem hinge_le_blockRecAt (P : Params) {dC : ℕ} (hP : BlockHyp P dC) {st : BlkSt} {B : ℕ}
    (hB : P.PX < B) (hBX : B ≤ P.PMAX) (h : ETInv P B st) {p : ℕ} (hp : p.Prime) (hBp : B ≤ p)
    (hpE : p < blockEnd P B) (γ : ℕ → ℕ) :
    hingeLoss P.m (delta0 P) p γ ≤ pv (blockRecAt P (sieve P.PMAX) st B).val := by
  have hE := ETInv_step P hP hB hBX h
  have hEX := blockEnd_le P B
  have hB2 : 2 ≤ B := by have := hP.one_le_PX; omega
  have hpX : p ≤ P.PMAX := by omega
  have hdn : deltaN P B < DDEN := deltaN_lt_DDEN P B
  have hdnB : deltaN P B = dC := hP.const B hB hBX
  have hdnp : deltaN P p = dC := hP.const p (by omega) hpX
  have hδp : delta0 P p = (deltaN P B : ℝ) / DDEN := by
    rw [delta0_of_le hpX, hdnp, hdnB, DDEN_real']
  have hdn0 : 0 < deltaN P B := by rw [hdnB]; exact hP.dC_pos
  have hsub : ∀ {f : ℕ → ℝ}, (∀ q, q.Prime → 1 ≤ f q) → ∀ {x : ℕ},
      ∏ q ∈ Nat.primesBelow (blockEnd P B), f q ≤ pv x →
      ∏ q ∈ Nat.primesBelow p, f q ≤ (x : ℝ) / ONE := fun hf1 x hx => by
    rw [← pv_eq_div_ONE]
    exact (prod_primesBelow_mono hpE.le _ fun q hq =>
      hf1 q (Nat.prime_of_mem_primesBelow hq)).trans hx
  unfold blockRecAt
  rw [pv_eq_div_ONE]
  exact hingeLoss_le_blockVal hp hB2 hBp hδp hdn0 hdn (fun q _ => delta0_le_one P q)
    (ν := tilt (delta0 P))
    (fun q hq => ⟨le_rfl, tilt_delta0_le_self P (Nat.prime_of_mem_primesBelow hq)⟩)
    (tailFactor (delta0 P)) (fhFactor (delta0 P)) (cubeFactor (delta0 P))
    (fun q hq γ => expect1_sq_le_tailFactor (Nat.prime_of_mem_primesBelow hq).one_lt
      (tilt_delta0_nonneg P q) γ)
    (fun q hq γ => expect1_le_fhFactor (Nat.prime_of_mem_primesBelow hq).one_lt
      (tilt_delta0_nonneg P q) (tilt_delta0_le_self P (Nat.prime_of_mem_primesBelow hq)) γ)
    (fun q hq γ => expect1_cube_le_cubeFactor (Nat.prime_of_mem_primesBelow hq).one_lt
      (tilt_delta0_nonneg P q) γ)
    (hsub (fun q hq => one_le_tailFactor0 P hq) hE.two)
    (hsub (fun q hq => one_le_fhFactor0 P hq) hE.five_halves)
    (hsub (fun q hq => one_le_cubeFactor0 P hq) hE.three) γ

/-! ### The loop -/

/-- **Specification of `blockLoop`** (with the sieve of `X`, from a block start `B > PX` with
enough fuel): the new blocks `L` form a chain from `B` to `max B (X + 1)`, `etaC` grows by
`Σ count·val`, `count ≥ #primes` in each block, and, if the running products satisfy `ETInv` at
`B`, every prime of a new block has hinge loss `≤ pv val` and `ETInv` holds at the end. -/
theorem blockLoop_spec (P : Params) {dC : ℕ} (hP : BlockHyp P dC) :
    ∀ (f : ℕ) (st : BlkSt) (B : ℕ), P.PX < B → P.PMAX + 1 ≤ B + f →
    ∃ L : List BlockRec,
      (blockLoop P (sieve P.PMAX) st B f).blocks.toList = st.blocks.toList ++ L ∧
      Chain B L (max B (P.PMAX + 1)) ∧
      (blockLoop P (sieve P.PMAX) st B f).etaC =
        st.etaC + (L.map fun b => b.count * b.val).sum ∧
      (∀ b ∈ L, #((Ico b.start b.stop).filter Nat.Prime) ≤ b.count) ∧
      (ETInv P B st →
        (∀ b ∈ L, ∀ p, p.Prime → b.start ≤ p → p < b.stop →
          ∀ γ, hingeLoss P.m (delta0 P) p γ ≤ pv b.val) ∧
        ETInv P (max B (P.PMAX + 1)) (blockLoop P (sieve P.PMAX) st B f))
  | 0, st, B, _, hf => by
    have hmax : max B (P.PMAX + 1) = B := max_eq_left (by omega)
    refine ⟨[], ?_, ?_, ?_, ?_, ?_⟩
    · rw [blockLoop_zero]; simp
    · rw [hmax]; rfl
    · rw [blockLoop_zero]; simp
    · simp
    · intro h
      rw [hmax, blockLoop_zero]
      exact ⟨by simp, h⟩
  | f + 1, st, B, hB, hf => by
    by_cases hBX : P.PMAX < B
    · have hmax : max B (P.PMAX + 1) = B := max_eq_left (by omega)
      rw [blockLoop_succ_of_gt _ _ _ _ _ hBX]
      refine ⟨[], by simp, by rw [hmax]; rfl, by simp, by simp, fun h => ?_⟩
      rw [hmax]
      exact ⟨by simp, h⟩
    · have hBX' : B ≤ P.PMAX := by omega
      have hBE := blockEnd_gt P hBX'
      have hEX := blockEnd_le P B
      have hmax : max B (P.PMAX + 1) = max (blockEnd P B) (P.PMAX + 1) := by
        rw [max_eq_right (by omega), max_eq_right hEX]
      rw [blockLoop_succ _ _ _ _ _ hBX']
      obtain ⟨L, hL1, hL2, hL3, hL4, hL5⟩ :=
        blockLoop_spec P hP f (blockStep P (sieve P.PMAX) st B) (blockEnd P B) (by omega)
          (by omega)
      refine ⟨blockRecAt P (sieve P.PMAX) st B :: L, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hL1, blockStep_blocks, Array.toList_push, List.append_assoc]
        rfl
      · rw [hmax]
        exact ⟨rfl, hBE, hL2⟩
      · rw [hL3, blockStep_etaC, List.map_cons, List.sum_cons, add_assoc]
      · intro b hb
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact card_primes_le_countUnmarked P.PMAX B (blockEnd P B)
        · exact hL4 b hb'
      · intro h
        have hE := ETInv_step P hP hB hBX' h
        obtain ⟨hL5a, hL5b⟩ := hL5 hE
        refine ⟨fun b hb p hp h1 h2 γ => ?_, by rw [hmax]; exact hL5b⟩
        rcases List.mem_cons.1 hb with rfl | hb'
        · exact hinge_le_blockRecAt P hP hB hBX' h hp h1 h2 γ
        · exact hL5a b hb' p hp h1 h2 γ

/-- The block phase of `run` as a chain: the list of blocks, from `PX + 1` to `X + 1`. -/
theorem blockPhase_spec (P : Params) {dC : ℕ} (hP : BlockHyp P dC) (ET2 ET25 ET3 : ℕ) :
    Chain (P.PX + 1) (blockPhase P ET2 ET25 ET3).blocks.toList (P.PMAX + 1) ∧
      (blockPhase P ET2 ET25 ET3).etaC =
        ((blockPhase P ET2 ET25 ET3).blocks.toList.map fun b => b.count * b.val).sum ∧
      (∀ b ∈ (blockPhase P ET2 ET25 ET3).blocks.toList,
        #((Ico b.start b.stop).filter Nat.Prime) ≤ b.count) ∧
      (ETHyp P ET2 ET25 ET3 →
        (∀ b ∈ (blockPhase P ET2 ET25 ET3).blocks.toList, ∀ p, p.Prime → b.start ≤ p →
          p < b.stop → ∀ γ, hingeLoss P.m (delta0 P) p γ ≤ pv b.val) ∧
        ETInv P (P.PMAX + 1) (blockPhase P ET2 ET25 ET3)) := by
  have hPX := hP.PX_le
  have hmax : max (P.PX + 1) (P.PMAX + 1) = P.PMAX + 1 := max_eq_right (by omega)
  obtain ⟨L, hL1, hL2, hL3, hL4, hL5⟩ :=
    blockLoop_spec P hP (P.PMAX + 1) ⟨0, ET2, ET25, ET3, #[]⟩ (P.PX + 1) (by omega) (by omega)
  have hbl : (blockPhase P ET2 ET25 ET3).blocks.toList = L := by
    unfold blockPhase; rw [hL1]; simp
  rw [hbl]
  refine ⟨by rw [← hmax]; exact hL2, by unfold blockPhase; rw [hL3]; simp, hL4, fun hET => ?_⟩
  -- the running products after the prime loop
  have hinv : ETInv P (P.PX + 1) ⟨0, ET2, ET25, ET3, #[]⟩ := by
    have hqP : ∀ q ∈ Nat.primesLE P.PX, q.Prime ∧ q ≤ P.PMAX := fun q hq =>
      ⟨Nat.prime_of_mem_primesLE hq, (Nat.mem_primesLE.1 hq).1.trans hPX⟩
    refine ⟨?_, ?_, ?_⟩
    · refine le_trans (prod_le_prod₀ (fun q hq => zero_le_one.trans
        (one_le_tailFactor0 P (hqP q hq).1)) fun q hq => ?_) hET.two
      obtain ⟨hqp, hqX⟩ := hqP q hq
      rw [pv_eq_div_ONE]
      exact tailFactor_le_fac2 hqp.two_le le_rfl (deltaN_lt_DDEN P q) (delta0_le_one P q)
        (le_of_eq (tilt_delta0_eq hqX))
    · refine le_trans (prod_le_prod₀ (fun q hq => zero_le_one.trans
        (one_le_fhFactor0 P (hqP q hq).1)) fun q hq => ?_) hET.five_halves
      obtain ⟨hqp, hqX⟩ := hqP q hq
      exact fhFactor_le_fac25 hqp.two_le le_rfl (deltaN_le P q) (tilt_delta0_nonneg P q)
        (le_of_eq (tilt_delta0_eq hqX))
    · refine le_trans (prod_le_prod₀ (fun q hq => zero_le_one.trans
        (one_le_cubeFactor0 P (hqP q hq).1)) fun q hq => ?_) hET.three
      obtain ⟨hqp, hqX⟩ := hqP q hq
      exact cubeFactor_le_fac3 hqp.two_le le_rfl (deltaN_lt_DDEN P q) (tilt_delta0_nonneg P q)
        (le_of_eq (tilt_delta0_eq hqX))
  obtain ⟨h1, h2⟩ := hL5 hinv
  rw [hmax] at h2
  exact ⟨h1, h2⟩

/-! ### The statements of `Interfaces.lean` -/

theorem list_sum_pv (L : List BlockRec) :
    (L.map fun b => (b.count : ℝ) * pv b.val).sum = pv ((L.map fun b => b.count * b.val).sum) := by
  induction L with
  | nil => simp [pv]
  | cons b L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, pv_add]
    unfold pv
    push_cast
    ring

/-- `blockCost` reads the `val` of the block containing `p`. -/
theorem blockCost_eq {blocks : Array BlockRec} {B E : ℕ} (h : Chain B blocks.toList E)
    {b : BlockRec} (hb : b ∈ blocks.toList) {p : ℕ} (h1 : b.start ≤ p) (h2 : p < b.stop) :
    blockCost blocks p = b.val := by
  unfold blockCost
  rw [← Array.find?_toList, Chain.find?_eq h b hb p h1 h2]

/-- **(CS-A, block costs)** Every prime `p ∈ (PX, X]` has hinge loss at most the `val` of its
block, for every uniform cap `N`, when the block phase starts from running products satisfying
`ETHyp`. -/
theorem blockPhase_cost_sound (P : Params) {dC : ℕ} (hP : BlockHyp P dC) {ET2 ET25 ET3 : ℕ}
    (hET : ETHyp P ET2 ET25 ET3) {p : ℕ} (hp : p.Prime) (hlo : P.PX < p) (hhi : p ≤ P.PMAX)
    (N : ℕ) :
    hingeLoss P.m (delta0 P) p (fun _ => N) ≤
      pv (blockCost (blockPhase P ET2 ET25 ET3).blocks p) := by
  obtain ⟨hch, -, -, h4⟩ := blockPhase_spec P hP ET2 ET25 ET3
  obtain ⟨b, hb, h1, h2⟩ := Chain.cover hch p (by omega) (by omega)
  rw [blockCost_eq hch hb h1 h2]
  exact (h4 hET).1 b hb p hp h1 h2 _

/-- **(CS-A, block sum)** `etaC` bounds the sum of the block costs over the primes in
`(PX, X]`. -/
theorem blockPhase_sum_le (P : Params) {dC : ℕ} (hP : BlockHyp P dC) (ET2 ET25 ET3 : ℕ) :
    ∑ p ∈ (Nat.primesLE P.PMAX).filter (P.PX < ·),
        pv (blockCost (blockPhase P ET2 ET25 ET3).blocks p) ≤
      pv (blockPhase P ET2 ET25 ET3).etaC := by
  obtain ⟨hch, hC, hcount, -⟩ := blockPhase_spec P hP ET2 ET25 ET3
  set bl := (blockPhase P ET2 ET25 ET3).blocks with hbl
  have hS : (Nat.primesLE P.PMAX).filter (P.PX < ·) = (Ico (P.PX + 1) (P.PMAX + 1)).filter Nat.Prime := by
    ext q
    simp only [mem_filter, Nat.mem_primesLE, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h3⟩, by omega⟩
  rw [hS]
  refine (Chain.sum_le _ hch hcount fun b hb p _ h1 h2 => le_of_eq (by
    rw [blockCost_eq hch hb h1 h2])).trans (le_of_eq ?_)
  rw [hC, list_sum_pv]

/-- **(CS-A, the T bound)** The final `ET2` bounds `T = ∏_{q ≤ X} tailFactor (delta0 P) q`. -/
theorem blockPhase_T_le (P : Params) {dC : ℕ} (hP : BlockHyp P dC) {ET2 ET25 ET3 : ℕ}
    (hET : ETHyp P ET2 ET25 ET3) :
    ∏ q ∈ Nat.primesLE P.PMAX, tailFactor (delta0 P) q ≤ pv (blockPhase P ET2 ET25 ET3).ET2 := by
  obtain ⟨-, -, -, h4⟩ := blockPhase_spec P hP ET2 ET25 ET3
  exact ((h4 hET).2).two

/-! ### The standing hypothesis for `fullParams` -/

/-- For `fullParams`, `δ = 4092/10000` for every `p ≥ 50000` (the last knot of the schedule). -/
theorem deltaN_fullParams_of_ge {p : ℕ} (hp : 50000 ≤ p) : deltaN fullParams p = 409200000 := by
  unfold deltaN
  have h1 : ¬ p < fullParams.PD := by simp [fullParams]; omega
  simp only [h1, ↓reduceIte]
  simp only [fullParams, knotDelta]
  have h2 : ¬ p ≤ 50 := by omega
  simp [h2, hp, dnOfTenThousandths, DNMAX]

/-- **`BlockHyp` for `fullParams`** with `dC = 409200000` (`δ = 0.4092` on `(PX, X]`). -/
theorem blockHyp_fullParams : BlockHyp fullParams 409200000 where
  one_le_PX := by decide
  PX_le := by decide
  dC_pos := by decide
  const := fun p hp _ => deltaN_fullParams_of_ge (by simp [fullParams] at hp; omega)

end MinModulus.CheckerSound.A
