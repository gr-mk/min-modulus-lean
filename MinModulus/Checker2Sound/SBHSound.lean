import MinModulus.Checker2Sound.SBHLeaf
import MinModulus.Checker2Sound.SBHDfs
import MinModulus.Checker2Sound.PrimsReal
import MinModulus.Checker2Sound.Tables
import MinModulus.CheckerMath.ComparisonBound

/-!
# `Checker2Sound.SBHSound` (agent L2-D): soundness of the S/B/H cost

STATUS: complete (fully proved; agent L2-D). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

**`D.sbhCost_sound`**: exactly the Interfaces statement `sbhCost_sound` (checked verbatim,
`SCRATCH/agents/lean2/l2d/StmtCheck.lean`). It is `sbhCost_sound_of` (the proof, from
`BuildTabSpec` = the Interfaces statement of `buildTab_sound` as a `Prop`) applied to L2-C's
`C.buildTab_sound` (`buildTabSpec_holds`).

Chain: `A.hingeLoss_eq_sbhLeaf` (L2-A: `hingeLoss = E_S[G]/((p−1)(1−δ_p))`) → `dfs_nodeVal`
(`SBHDfs`: the DFS accumulates `≥ E_S[G]`, leaves via `leafValue_sound`, pruning via
`A.expVal_le`) → the final rounding `cost = ⌈(leaf + prune)·2^14·10^9/((p−1)(10^9 − dn))⌉`;
caps `N < KH + 61` by `CheckerMath.hingeLoss_le_of_forall_ge`.
-/

namespace MinModulus.Checker2Sound.D

open MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.Checker2Math MinModulus.Smooth
  MinModulus.CheckerMath MinModulus.Main Finset

/-! ### The code of `sbhCost`, with named pieces -/

/-- The `DfsCfg` built by `sbhCost` (the same definition, with projections instead of the
pattern-matching `let`s). -/
def sbhCfg (P : Params2) (p dn : ℕ) (primes dns : Array ℕ) (k : ℕ) (H : HState) : DfsCfg :=
  let N1 := cdiv P.m p
  let N2 := cdiv P.m (p * p)
  let y := splitY P.YB N1 N2
  let iS := min (countLt primes y) k
  let iB := min (countLt primes N1) k
  let iB := max iS iB
  let Sq := primes.extract 0 iS
  let Sdn := dns.extract 0 iS
  let Bq := primes.extract iS iB
  let Bdn := dns.extract iS iB
  let cd := cdTable P.m p N1
  let kk := Sq.map (kkOf · N1)
  let st := strides kk
  let pd := patternData Sq kk Bq cd N1 st.2
  let ET := prodUp (fun i => facE1u Bq[i]! Bdn[i]!) H.E 0 Bq.size
  let pmB := (Array.range Bq.size).map fun i => pmArr Bq[i]! Bdn[i]! (P.KH - 1)
  let tp1int := dn * (p - 1) / DDEN
  let tabs := pd.2.2.map fun a => buildTab a Bq Bdn pmB H.D P.KH tp1int
  let acut := Sq.map acut60
  let pmS := (Array.range Sq.size).map fun j => pmArr Sq[j]! Sdn[j]! acut[j]!
  let hS := (Array.range Sq.size).map fun j => hArr Sq[j]! Sdn[j]! (acut[j]! + 1)
  let Rrest := (Array.range (Sq.size + 1)).map fun j =>
    prodUp (fun i => facE1u Sq[i]! Sdn[i]!) ONE2 j (Sq.size - j)
  let REW := Rrest.map fun r => cdiv (r * ET) (ONE2 <<< 14)
  { nS := Sq.size, pm := pmS, acut, h := hS, REW, kk, stride := st.1, ETW := cdiv ET 16384,
    epsAbs := REW[0]! >>> P.epsShift, patF := pd.1, patProf := pd.2.1, tabs,
    tp1 := dn * (p - 1) * W48 / DDEN, om := W48 - cdiv W48 p, omP := (W48 - cdiv W48 p) <<< 14 }

/-- The final accumulator of the DFS of `sbhCost`. -/
def sbhAcc (P : Params2) (p dn : ℕ) (primes dns : Array ℕ) (k : ℕ) (H : HState) : DfsAcc :=
  dfsNode (sbhCfg P p dn primes dns k H) 100000 0 ONE2 1 0 ⟨0, 0, 0, true⟩

theorem sbhCost_cost (P : Params2) (p dn : ℕ) (primes dns : Array ℕ) (k : ℕ) (H : HState) :
    (sbhCost P p dn primes dns k H).cost =
      cdiv ((((sbhAcc P p dn primes dns k H).leaf + (sbhAcc P p dn primes dns k H).prune) <<< 14) *
        DDEN) ((p - 1) * (DDEN - dn)) := rfl

theorem sbhCost_ok (P : Params2) (p dn : ℕ) (primes dns : Array ℕ) (k : ℕ) (H : HState) :
    (sbhCost P p dn primes dns k H).ok =
      (decide (cdiv P.m p ≤ splitY P.YB (cdiv P.m p) (cdiv P.m (p * p)) *
          splitY P.YB (cdiv P.m p) (cdiv P.m (p * p))) &&
        decide (cdiv P.m (p * p) ≤ splitY P.YB (cdiv P.m p) (cdiv P.m (p * p))) &&
        decide (2 ≤ cdiv P.m p) &&
        ((H.lo == H.hi || (H.lo == max (min (countLt primes (splitY P.YB (cdiv P.m p)
            (cdiv P.m (p * p)))) k) (min (countLt primes (cdiv P.m p)) k) && H.hi == k)) &&
          (H.lo != H.hi || max (min (countLt primes (splitY P.YB (cdiv P.m p)
            (cdiv P.m (p * p)))) k) (min (countLt primes (cdiv P.m p)) k) == k)) &&
        (sbhAcc P p dn primes dns k H).ok && decide (dn < DDEN) && decide (2 ≤ p)) := rfl

/-! ### Helpers -/

theorem pv_ONE2' : pv ONE2 = 1 := by
  unfold pv; rw [ONE2_eq, ONE_real']; norm_num

/-- `prodUp` rounds up: `pv acc · ∏_{l ∈ [i, i+n)} pv (f l) ≤ pv (prodUp f acc i n)`. -/
theorem prodUp_ge (f : ℕ → ℕ) :
    ∀ n acc i, pv acc * ∏ l ∈ Ico i (i + n), pv (f l) ≤ pv (prodUp f acc i n) := by
  intro n
  induction n with
  | zero => intro acc i; simp [prodUp]
  | succ n ih =>
    intro acc i
    simp only [prodUp]
    rw [show i + (n + 1) = (i + 1) + n by omega, prod_eq_prod_Ico_succ_bot (by omega)]
    have h0 : 0 ≤ ∏ l ∈ Ico (i + 1) (i + 1 + n), pv (f l) := prod_nonneg fun _ _ => pv_nonneg' _
    calc pv acc * (pv (f i) * ∏ l ∈ Ico (i + 1) (i + 1 + n), pv (f l))
        = (pv acc * pv (f i)) * ∏ l ∈ Ico (i + 1) (i + 1 + n), pv (f l) := by ring
      _ ≤ pv (mulUp acc (f i)) * ∏ l ∈ Ico (i + 1) (i + 1 + n), pv (f l) :=
          mul_le_mul_of_nonneg_right (pv_mul_le_mulUp' _ _) h0
      _ ≤ pv (prodUp f (mulUp acc (f i)) (i + 1) n) := ih _ _

/-- The mixed-radix bound: a pattern index is below `npat`. -/
theorem sum_lt_sprod (kk : Array ℕ) (e : ℕ → ℕ) :
    ∀ n, (∀ i < n, e i ≤ kk[i]!) → ∑ i ∈ range n, e i * sprod kk i < sprod kk n := by
  intro n
  induction n with
  | zero => intro _; simp [sprod]
  | succ n ih =>
    intro he
    rw [sum_range_succ]
    have h1 := ih (fun i hi => he i (by omega))
    have h2 := he n (by omega)
    have e1 : sprod kk (n + 1) = sprod kk n * (kk[n]! + 1) := by
      unfold sprod; rw [prod_range_succ]
    rw [e1]
    have : e n * sprod kk n ≤ kk[n]! * sprod kk n := Nat.mul_le_mul_right _ h2
    nlinarith

/-- The profile of a table sums to its `bm`. -/
theorem sum_profileFn {Bq a : Array ℕ} (hnd : Bq.toList.Nodup) (ha : a.size = Bq.size) :
    ∑ q ∈ Bq.toList.toFinset, profileFn Bq a q = a.foldl (· + ·) 0 := by
  rw [List.sum_toFinset _ hnd]
  have hmap : Bq.toList.map (profileFn Bq a) = a.toList := by
    apply List.ext_getElem (by simp [ha])
    intro i h1 h2
    rw [List.getElem_map]
    unfold profileFn
    rw [hnd.idxOf_getElem i (by simpa using h1), getElem_toList_eq_getElem!]
  rw [hmap, ← Array.foldl_toList]
  have := foldl_add_eq id a.toList 0
  rw [List.map_id, zero_add] at this
  exact this.symm

/-- `idxSet` as an image. -/
theorem idxSet_eq_image {P : Params2} {lo hi : ℕ} (hhi : hi ≤ (primes2 P).size) :
    idxSet P lo hi = (Ico lo hi).image (fun i => (primes2 P)[i]!) := by
  ext q
  rw [mem_idxSet, mem_image]
  constructor
  · rintro ⟨i, h1, h2, -, rfl⟩; exact ⟨i, mem_Ico.2 ⟨h1, h2⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rw [mem_Ico] at hi
    exact ⟨i, hi.1, hi.2, by omega, rfl⟩

/-- L2-A's `sufSet` for the prime array is `idxSet`. -/
theorem sufSet_eq_idxSet {P : Params2} {n : ℕ} (hn : n ≤ (primes2 P).size) (j : ℕ) :
    A.sufSet (fun i => (primes2 P)[i]!) n j = idxSet P j n := by
  unfold A.sufSet
  rw [idxSet_eq_image hn]

theorem dns2_get {P : Params2} {i : ℕ} (hi : i < (primes2 P).size) :
    (dns2 P)[i]! = deltaN2 P (primes2 P)[i]! := by
  unfold dns2; rw [getElem!_map _ _ hi]

theorem dns2_extract (P : Params2) (a b : ℕ) :
    (dns2 P).extract a b = ((primes2 P).extract a b).map (deltaN2 P) := by
  unfold dns2; rw [Array.map_extract]

/-- The `E[v+1]` bounds of a slice of the prime array, as a product over `idxSet`. -/
theorem prod_facE1u_ge {P : Params2} (hPX : P.PX ≤ P.X) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ (primes2 P).size) {i len : ℕ} (hi : i + len ≤ b - a) :
    ∏ q ∈ idxSet P (a + i) (a + i + len), (1 + nu2 P q / ((q : ℝ) - 1)) ≤
      ∏ l ∈ Ico i (i + len),
        pv (facE1u ((primes2 P).extract a b)[l]! ((dns2 P).extract a b)[l]!) := by
  have hmem : ∀ l ∈ Ico i (i + len), a + l < (primes2 P).size := fun l hl => by
    rw [mem_Ico] at hl; omega
  have hget : ∀ l ∈ Ico i (i + len), ((primes2 P).extract a b)[l]! = (primes2 P)[a + l]! :=
    fun l hl => by rw [mem_Ico] at hl; rw [getElem!_extract _ (by omega)]
  have hgetd : ∀ l ∈ Ico i (i + len), ((dns2 P).extract a b)[l]! = deltaN2 P (primes2 P)[a + l]! :=
    fun l hl => by
      rw [mem_Ico] at hl
      rw [getElem!_extract _ (by unfold dns2; simp; omega), dns2_get (by omega)]
  have hle : ∏ l ∈ Ico i (i + len), (1 + nu2 P (primes2 P)[a + l]! /
        (((primes2 P)[a + l]! : ℕ) - 1 : ℝ)) ≤
      ∏ l ∈ Ico i (i + len),
        pv (facE1u ((primes2 P).extract a b)[l]! ((dns2 P).extract a b)[l]!) := by
    refine prod_le_prod₀ (fun l hl => ?_) (fun l hl => ?_)
    · have h2 := two_le_primes2 (hmem l hl)
      have hX := (primes2_le (hmem l hl)).trans hPX
      have hν := (C.nu2_mem h2 hX).1
      have : (1 : ℝ) < ((primes2 P)[a + l]! : ℕ) := by exact_mod_cast h2
      have : 0 ≤ nu2 P (primes2 P)[a + l]! / (((primes2 P)[a + l]! : ℕ) - 1 : ℝ) :=
        div_nonneg hν (by linarith)
      linarith
    · rw [hget l hl, hgetd l hl]
      exact C.facE1u_nu2_ge (two_le_primes2 (hmem l hl)) ((primes2_le (hmem l hl)).trans hPX)
  refine le_trans (le_of_eq ?_) hle
  have hshift : ∀ g : ℕ → ℝ, ∏ x ∈ Ico (a + i) (a + i + len), g x =
      ∏ l ∈ Ico i (i + len), g (a + l) := by
    intro g
    rw [show a + i + len = (i + len) + a by ring, show a + i = i + a by ring, ← prod_Ico_add']
    exact prod_congr rfl fun l _ => by rw [add_comm]
  rw [idxSet_eq_image (by omega), prod_image, hshift]
  intro x hx y hy hxy
  rw [coe_Ico, Set.mem_Ico] at hx hy
  exact primes2_inj (by omega) (by omega) hxy


/-! ### Rounding of the final quantities -/

theorem DDEN_real' : ((DDEN : ℕ) : ℝ) = 10 ^ 9 := by unfold DDEN; norm_num

/-- `ETW = ⌈ET/2^14⌉` is an upper W-value of the P-value `ET`. -/
theorem pv_le_wv_cdiv (x : ℕ) : pv x ≤ wv (cdiv x 16384) := by
  have h := cdiv_ge (a := x) (b := 16384) (by norm_num)
  unfold pv wv
  rw [le_div_iff₀ (by positivity)]
  have e : (x : ℝ) / 2 ^ 62 * 2 ^ 48 = (x : ℝ) / ((16384 : ℕ) : ℝ) := by norm_num; ring
  rw [e]; exact h

/-- `REW = ⌈R·ET/2^76⌉` is an upper W-value of `pv R · pv ET`. -/
theorem pv_mul_pv_le_REW (x y : ℕ) : pv x * pv y ≤ wv (cdiv (x * y) (ONE2 <<< 14)) := by
  have hO : ((ONE2 <<< 14 : ℕ) : ℝ) = 2 ^ 76 := by
    rw [Nat.shiftLeft_eq, Nat.cast_mul, ONE2_eq, ONE_real']; norm_num
  have h := cdiv_ge (a := x * y) (b := ONE2 <<< 14) (by rw [Nat.shiftLeft_eq, ONE2_eq, ONE_eq]; positivity)
  rw [hO] at h
  unfold pv wv
  rw [le_div_iff₀ (by positivity)]
  push_cast at h
  have e : (x : ℝ) / 2 ^ 62 * ((y : ℝ) / 2 ^ 62) * 2 ^ 48 = (x : ℝ) * y / 2 ^ 76 := by ring
  rw [e]; exact h

/-- `tp1 = ⌊dn (p−1) 2^48 / 10^9⌋` is a lower W-value of `δ_p (p − 1)`. -/
theorem wv_tp1_le (dn p : ℕ) (hp : 1 ≤ p) :
    wv (dn * (p - 1) * W48 / DDEN) ≤ (dn : ℝ) / 10 ^ 9 * ((p : ℝ) - 1) := by
  have h := Nat.cast_div_le (α := ℝ) (m := dn * (p - 1) * W48) (n := DDEN)
  unfold wv
  rw [div_le_iff₀ (by positivity)]
  refine h.trans (le_of_eq ?_)
  rw [DDEN_real', Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp, W48_real]
  push_cast
  ring

/-- `om = 2^48 − ⌈2^48/p⌉` is a lower W-value of `ω = 1 − 1/p`. -/
theorem wv_om_le {p : ℕ} (hp : 1 ≤ p) : wv (W48 - cdiv W48 p) ≤ 1 - 1 / (p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one hp0]; exact_mod_cast hp
  have hc := cdiv_ge (a := W48) (b := p) (by omega)
  rcases le_total (cdiv W48 p) W48 with h | h
  · unfold wv
    rw [Nat.cast_sub h, W48_real]
    rw [W48_real] at hc
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ 48 / p = 1 / p * 2 ^ 48 := by ring
    nlinarith
  · rw [Nat.sub_eq_zero_of_le h]
    simp only [wv, Nat.cast_zero, zero_div]
    linarith

/-- **The final rounding** of `sbhCost`: `cost = ⌈(L·2^14)·10^9 / ((p−1)(10^9 − dn))⌉` is an upper
P-value of `wv L / ((p − 1)(1 − dn/10^9))`. -/
theorem wv_div_le_cost {p dn : ℕ} (hp : 2 ≤ p) (hdn : dn < DDEN) (L : ℕ) {δ : ℝ}
    (hδ : δ = (dn : ℝ) / 10 ^ 9) :
    wv L / (((p : ℝ) - (1 : ℝ)) * ((1 : ℝ) - δ)) ≤
      pv (cdiv ((L <<< 14) * DDEN) ((p - 1) * (DDEN - dn))) := by
  subst hδ
  have hD : 0 < (p - 1) * (DDEN - dn) := Nat.mul_pos (by omega) (by omega)
  have h := cdiv_ge (a := (L <<< 14) * DDEN) hD
  have hdn' : (dn : ℝ) < 10 ^ 9 := by
    have h' : (dn : ℝ) < ((DDEN : ℕ) : ℝ) := by exact_mod_cast hdn
    rwa [DDEN_real'] at h'
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have e1 : (((p - 1) * (DDEN - dn) : ℕ) : ℝ) = ((p : ℝ) - 1) * (10 ^ 9 - dn) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub hdn.le, DDEN_real']
    push_cast; ring
  have e2 : (((L <<< 14) * DDEN : ℕ) : ℝ) = (L : ℝ) * 2 ^ 14 * 10 ^ 9 := by
    rw [Nat.cast_mul, Nat.shiftLeft_eq, DDEN_real']; push_cast; ring
  rw [e1, e2] at h
  unfold pv wv
  rw [le_div_iff₀ (by positivity)]
  refine le_trans (le_of_eq ?_) h
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (10 : ℝ) ^ 9 - dn ≠ 0 := by linarith
  have e3 : (1 : ℝ) - (dn : ℝ) / 10 ^ 9 = ((10 : ℝ) ^ 9 - dn) / 10 ^ 9 := by field_simp
  rw [e3]
  field_simp

/-! ### `buildTab_sound`, restated -/

/-- The Interfaces statement of L2-C's `buildTab_sound`, verbatim, as a `Prop`. -/
def BuildTabSpec : Prop :=
  ∀ (P : Params2), P.PX ≤ P.X → ∀ {H : HState}, HValid P H →
    ∀ {Bq Bdn a : Array ℕ}, (∀ q ∈ Bq.toList, q.Prime ∧ q ≤ P.X) → Bq.toList.Nodup →
    Disjoint Bq.toList.toFinset (idxSet P H.lo H.hi) → Bdn = Bq.map (deltaN2 P) →
    a.size = Bq.size → ∀ (tp1int : ℕ) (N : ℕ), P.KH ≤ N →
    let tab := buildTab a Bq Bdn ((Array.range Bq.size).map fun i =>
      pmArr Bq[i]! Bdn[i]! (P.KH - 1)) H.D P.KH tp1int
    let R := Bq.toList.toFinset ∪ idxSet P H.lo H.hi
    tab.bm = a.foldl (· + ·) 0 ∧
      wv tab.EbW ≤ ∑ q ∈ Bq.toList.toFinset, (profileFn Bq a q : ℝ) * (nu2 P q / q) ∧
      ∀ b, b ≤ tab.bm → ∀ c : ℝ, 0 ≤ c → ⌊c⌋₊ ≤ tab.K →
        ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * lawJoint R (profileFn Bq a) (nu2 P) (fun _ => N) j b ≤
          c * pv (tabS0 tab b ⌊c⌋₊) - wv (tabS1W tab b ⌊c⌋₊)


/-! ### The main theorem -/

/-- **`sbhCost_sound`** from `BuildTabSpec` (L2-C's `buildTab_sound`). -/
theorem sbhCost_sound_of (hBT : BuildTabSpec) (P : Params2) (hPX : P.PX ≤ P.X) {k : ℕ}
    (hk : k < (primes2 P).size) (hN1 : 3 ≤ cdiv P.m (primes2 P)[k]!) {H : HState}
    (hH : HValid P H)
    (hok : (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).ok = true) (N : ℕ) :
    hingeLoss P.m (delta2 P) (primes2 P)[k]! (fun _ => N) ≤
      pv (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).cost := by
  have hpp : ((primes2 P)[k]!).Prime := primes2_prime hk
  have hδ0 : ∀ q, q.Prime → 0 ≤ delta2 P q := deltaPairR_nonneg _
  have hδ1 : ∀ q, q.Prime → delta2 P q ≤ 1 / 2 := deltaPairR_le_half fun q _ => by
    unfold deltaCert2
    split_ifs
    · norm_num
    · exact C.two_deltaN2_le P q
  refine hingeLoss_le_of_forall_ge hpp hδ0 hδ1 (P.KH + 61) (fun N hN => ?_) N
  -- names for the code's quantities
  set p := (primes2 P)[k]! with hp_def
  set dn := (dns2 P)[k]! with hdn_def
  have hp2 : 2 ≤ p := hpp.two_le
  have hpX : p ≤ P.X := (primes2_le hk).trans hPX
  have hdn : dn = deltaN2 P p := dns2_get hk
  have hδp : delta2 P p = (dn : ℝ) / 10 ^ 9 := by rw [C.delta2_of_le hpX, hdn]
  rw [sbhCost_ok] at hok
  rw [sbhCost_cost]
  set N1 := cdiv P.m p with hN1def
  set y := splitY P.YB N1 (cdiv P.m (p * p)) with hydef
  set iS := min (countLt (primes2 P) y) k with hiSdef
  set iB := max iS (min (countLt (primes2 P) N1) k) with hiBdef
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hyy, hy2⟩, -⟩, hokH⟩, haccok⟩, hdnD⟩, -⟩ := hok
  obtain ⟨hSB', hBk', -, hBy', hHN1'⟩ := sbh_split hk y N1
  have hSB : iS ≤ iB := hSB'
  have hBk : iB ≤ k := hBk'
  have hBy : ∀ i, iS ≤ i → i < iB → y ≤ (primes2 P)[i]! ∧ (primes2 P)[i]! < N1 := hBy'
  have hHN1 : ∀ i, iB ≤ i → i < k → N1 ≤ (primes2 P)[i]! := hHN1'
  have hiSk : iS ≤ k := hSB.trans hBk
  have hiSsize : iS ≤ (primes2 P).size := by omega
  -- the sets `S`, `B`, `H`
  set S := idxSet P 0 iS with hS_def
  set B := idxSet P iS iB with hB_def
  set Hs := idxSet P iB k with hHs_def
  have hHset : idxSet P H.lo H.hi = Hs := by
    obtain ⟨h1 | ⟨h1, h2⟩, h3⟩ := hokH
    · rcases h3 with h3 | h3
      · exact absurd h1 h3
      · rw [h1, idxSet_empty le_rfl, hHs_def, h3, idxSet_empty le_rfl]
    · rw [h1, h2]
  have hpart : Nat.primesBelow p = S ∪ (B ∪ Hs) := by
    rw [primesBelow_eq_idxSet hk, idxSet_union (Nat.zero_le iS) hiSk, idxSet_union hSB hBk]
  have hdisj : Disjoint S (B ∪ Hs) :=
    Finset.disjoint_union_right.2 ⟨idxSet_disjoint le_rfl, idxSet_disjoint hSB⟩
  have hBH : Disjoint B Hs := idxSet_disjoint le_rfl
  have hBprop : ∀ q ∈ B, y ≤ q ∧ q * p < P.m := by
    intro q hq
    obtain ⟨i, h1, h2, -, rfl⟩ := mem_idxSet.1 hq
    obtain ⟨hy', hN⟩ := hBy i h1 h2
    exact ⟨hy', (lt_cdiv_iff (by omega)).1 hN⟩
  have hHprop : ∀ q ∈ Hs, P.m ≤ q * p := by
    intro q hq
    obtain ⟨i, h1, h2, -, rfl⟩ := mem_idxSet.1 hq
    have h3 := hHN1 i h1 h2
    by_contra hc
    have := (lt_cdiv_iff (a := (primes2 P)[i]!) (m := P.m) (b := p) (by omega)).2 (not_le.1 hc)
    omega
  have hy2' : P.m ≤ y * y * p :=
    (le_cdiv_mul P.m p (by omega)).trans (Nat.mul_le_mul_right p hyy)
  have hy1' : P.m ≤ y * p ^ 2 := by
    calc P.m ≤ cdiv P.m (p * p) * (p * p) := le_cdiv_mul P.m (p * p) (by positivity)
      _ ≤ y * (p * p) := Nat.mul_le_mul_right _ hy2
      _ = y * p ^ 2 := by ring
  rw [A.hingeLoss_eq_sbhLeaf hpp hpart hdisj hBprop hHprop hy2' hy1' (fun _ => N)]
  refine le_trans ?_ (wv_div_le_cost hp2 hdnD _ hδp)
  have hden : 0 < ((p : ℝ) - 1) * (1 - delta2 P p) := by
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp2
    have h2 := hδ1 p hpp
    exact mul_pos (by linarith) (by linarith)
  refine div_le_div_of_nonneg_right ?_ hden.le
  -- the code's arrays
  set Sq := (primes2 P).extract 0 iS with hSq_def
  set Sdn := (dns2 P).extract 0 iS with hSdn_def
  set Bq := (primes2 P).extract iS iB with hBq_def
  set Bdn := (dns2 P).extract iS iB with hBdn_def
  set kk := Sq.map (kkOf · N1) with hkk_def
  set cd := cdTable P.m p N1 with hcd_def
  set ET := prodUp (fun i => facE1u Bq[i]! Bdn[i]!) H.E 0 Bq.size with hET_def
  set c := sbhCfg P p dn (primes2 P) (dns2 P) k H with hc_def
  have hSqsize : Sq.size = iS := extract0_size hiSsize
  have hSqget : ∀ i < iS, Sq[i]! = (primes2 P)[i]! := fun i hi => extract0_get hiSsize hi
  have hSdnget : ∀ i < iS, Sdn[i]! = deltaN2 P (primes2 P)[i]! := fun i hi => by
    rw [hSdn_def, dns2_extract, getElem!_map _ _ (by rw [extract0_size hiSsize]; omega),
      extract0_get hiSsize hi]
  have hkksize : kk.size = iS := by rw [hkk_def, Array.size_map, hSqsize]
  have hkkget : ∀ i < iS, kk[i]! = kkOf (primes2 P)[i]! N1 := fun i hi => by
    rw [hkk_def, getElem!_map _ _ (by omega), hSqget i hi]
  have hBsize : Bq.size = iB - iS := by rw [hBq_def, size_extract']; omega
  have hBset : Bq.toList.toFinset = B := extract_toList_toFinset iS iB
  have hBqmem : ∀ q ∈ Bq.toList, q.Prime ∧ q ≤ P.X := fun q hq => by
    have : q ∈ B := by rw [← hBset]; exact List.mem_toFinset.2 hq
    exact ⟨idxSet_prime this, (idxSet_le_PX this).trans hPX⟩
  have hBqnd : Bq.toList.Nodup := by
    rw [hBq_def, Array.toList_extract, List.extract_eq_take_drop]
    exact ((primes2_nodup P).sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)
  -- the fields of the configuration (definitional)
  have hc_nS : c.nS = iS := hSqsize
  have hc_acut : ∀ j < iS, c.acut[j]! = acut60 (primes2 P)[j]! := fun j hj => by
    show (Sq.map acut60)[j]! = _
    rw [getElem!_map _ _ (by omega), hSqget j hj]
  have hc_kk : ∀ j < iS, c.kk[j]! = kkOf (primes2 P)[j]! N1 := hkkget
  have hc_stride : ∀ j < iS, c.stride[j]! = sprod kk j := fun j hj =>
    (strides_spec kk).2.2 j (by omega)
  have hc_pm : ∀ j < iS, c.pm[j]! =
      pmArr (primes2 P)[j]! (deltaN2 P (primes2 P)[j]!) (acut60 (primes2 P)[j]!) := fun j hj => by
    show ((Array.range Sq.size).map fun j => pmArr Sq[j]! Sdn[j]! (Sq.map acut60)[j]!)[j]! = _
    rw [getElem!_range_map _ (by omega), getElem!_map _ _ (by omega), hSqget j hj, hSdnget j hj]
  have hc_h : ∀ j < iS, c.h[j]! =
      hArr (primes2 P)[j]! (deltaN2 P (primes2 P)[j]!) (acut60 (primes2 P)[j]! + 1) := fun j hj => by
    show ((Array.range Sq.size).map fun j => hArr Sq[j]! Sdn[j]! ((Sq.map acut60)[j]! + 1))[j]! = _
    rw [getElem!_range_map _ (by omega), getElem!_map _ _ (by omega), hSqget j hj, hSdnget j hj]
  have hc_REW : ∀ j < iS, c.REW[j + 1]! =
      cdiv (prodUp (fun i => facE1u Sq[i]! Sdn[i]!) ONE2 (j + 1) (Sq.size - (j + 1)) * ET)
        (ONE2 <<< 14) := fun j hj => by
    show (((Array.range (Sq.size + 1)).map fun j =>
      prodUp (fun i => facE1u Sq[i]! Sdn[i]!) ONE2 j (Sq.size - j)).map
        fun r => cdiv (r * ET) (ONE2 <<< 14))[j + 1]! = _
    rw [getElem!_map _ _ (by simp; omega), getElem!_range_map _ (by omega)]
  -- tilts
  have hνpr : ∀ q, q.Prime → q ≤ P.X → 0 ≤ nu2 P q ∧ nu2 P q ≤ q := fun q hq hqX =>
    C.nu2_mem hq.two_le hqX
  have hνR : ∀ q ∈ B ∪ Hs, 0 ≤ nu2 P q ∧ nu2 P q ≤ q := fun q hq => by
    rcases mem_union.1 hq with h | h
    · exact hνpr q (idxSet_prime h) ((idxSet_le_PX h).trans hPX)
    · exact hνpr q (idxSet_prime h) ((idxSet_le_PX h).trans hPX)
  have hR1 : ∀ q ∈ B ∪ Hs, 1 < q := fun q hq => by
    rcases mem_union.1 hq with h | h
    · exact (idxSet_prime h).one_lt
    · exact (idxSet_prime h).one_lt
  -- `E[T] ≤ pv ET`
  have hprodR : ∏ q ∈ B ∪ Hs, (1 + nu2 P q / ((q : ℝ) - 1)) ≤ pv ET := by
    rw [prod_union hBH]
    have h1 := hH.mean
    rw [hHset] at h1
    have h2 := prod_facE1u_ge (P := P) (a := iS) (b := iB) hPX hSB (by omega) (i := 0)
      (len := Bq.size) (by omega)
    rw [show iS + 0 + Bq.size = iB by omega, show iS + 0 = iS by omega,
      show 0 + Bq.size = Bq.size by omega] at h2
    have h3 := prodUp_ge (fun i => facE1u Bq[i]! Bdn[i]!) Bq.size H.E 0
    rw [zero_add] at h3
    have hB0 : 0 ≤ ∏ q ∈ B, (1 + nu2 P q / ((q : ℝ) - 1)) := prod_nonneg fun q hq => by
      have := hR1 q (mem_union_left _ hq); have := (hνR q (mem_union_left _ hq)).1
      have : (1 : ℝ) < q := by exact_mod_cast hR1 q (mem_union_left _ hq)
      have : 0 ≤ nu2 P q / ((q : ℝ) - 1) := div_nonneg (hνR q (mem_union_left _ hq)).1 (by linarith)
      linarith
    have hH0 : 0 ≤ ∏ q ∈ Hs, (1 + nu2 P q / ((q : ℝ) - 1)) := prod_nonneg fun q hq => by
      have : (1 : ℝ) < q := by exact_mod_cast hR1 q (mem_union_right _ hq)
      have : 0 ≤ nu2 P q / ((q : ℝ) - 1) := div_nonneg (hνR q (mem_union_right _ hq)).1 (by linarith)
      linarith
    calc (∏ q ∈ B, (1 + nu2 P q / ((q : ℝ) - 1))) * ∏ q ∈ Hs, (1 + nu2 P q / ((q : ℝ) - 1))
        = (∏ q ∈ Hs, (1 + nu2 P q / ((q : ℝ) - 1))) * ∏ q ∈ B, (1 + nu2 P q / ((q : ℝ) - 1)) :=
          mul_comm _ _
      _ ≤ pv H.E * ∏ l ∈ Ico 0 Bq.size, pv (facE1u Bq[l]! Bdn[l]!) :=
          mul_le_mul h1 h2 hB0 (pv_nonneg' _)
      _ ≤ pv ET := h3
  -- the leaf function
  set G : (ℕ → ℕ) → ℝ := fun u => A.sbhLeaf (B ∪ Hs) (nu2 P) (fun _ => N)
      (A.sbhProfile p P.m B (smooth S u)) (tauN S u)
      (Fsum p P.m (smooth S u) + delta2 P p * ((p : ℝ) - 1)) (1 - 1 / (p : ℝ)) with hG_def
  have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hω0 : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1r
    linarith
  have hβ0 : ∀ w, 0 ≤ Fsum p P.m (smooth S w) + delta2 P p * ((p : ℝ) - 1) := fun w => by
    have h1 := A.Fsum_nonneg (show 1 ≤ p by omega) P.m (smooth S w)
    have h2 := hδ0 p hpp
    have h3 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    exact add_nonneg h1 (mul_nonneg h2 h3)
  have hG0 : ∀ w, 0 ≤ G w := fun w => A.sbhLeaf_nonneg hνR _ _ _ _ _
  have hG : ∀ w, G w ≤ pv ET * (tauN S w : ℝ) := by
    intro w
    have h := A.sbhLeaf_le_prod hR1 hνR (fun _ => N) (A.sbhProfile p P.m B (smooth S w))
      (Nat.cast_nonneg (tauN S w)) (hβ0 w) hω0
    calc G w ≤ (tauN S w : ℝ) * ∏ q ∈ B ∪ Hs, (1 + nu2 P q / ((q : ℝ) - 1)) := h
      _ ≤ (tauN S w : ℝ) * pv ET := mul_le_mul_of_nonneg_left hprodR (Nat.cast_nonneg _)
      _ = pv ET * (tauN S w : ℝ) := mul_comm _ _
  have hsuf : A.sufSet (fun i => (primes2 P)[i]!) iS 0 = S := sufSet_eq_idxSet hiSsize 0
  -- the leaves
  have hleaf : ∀ (u : ℕ → ℕ) (pat P' : ℕ) (acc : DfsAcc),
      (∀ i < iS, u ((primes2 P)[i]!) ≤ c.acut[i]!) →
      pat = ∑ i ∈ range iS, min (u ((primes2 P)[i]!)) (kkOf (primes2 P)[i]! N1) * sprod kk i →
      (leafAdd c P' (tauN (A.sufSet (fun i => (primes2 P)[i]!) iS 0) u) pat acc).ok = true →
      accW acc + pv P' * G u ≤
        accW (leafAdd c P' (tauN (A.sufSet (fun i => (primes2 P)[i]!) iS 0) u) pat acc) := by
    intro u pat P' acc hu hpat hokL
    rw [hsuf] at hokL ⊢
    set τ := tauN S u with hτ_def
    rw [leafAdd_eq] at hokL ⊢
    simp only [Bool.and_eq_true] at hokL
    obtain ⟨-, hlv⟩ := hokL
    -- the pattern of the leaf `u`
    have hu60 : ∀ i < iS, u ((primes2 P)[i]!) ≤ 60 := fun i hi =>
      (hu i hi).trans (by rw [hc_acut i hi]; exact C.acut60_le (two_le_primes2 (by omega)))
    obtain ⟨hnd0, hmem0⟩ := smallDivs_leaf (P := P) hiSsize (m := P.m) (p := p) (by omega)
      (by omega) hu60
    have hnd : (smallDivs Sq kk N1 pat).toList.Nodup := by rw [hpat]; exact hnd0
    have hmem : ∀ x, x ∈ (smallDivs Sq kk N1 pat).toList ↔ x ∣ smooth S u ∧ x * p < P.m := by
      rw [hpat]; exact hmem0
    have hpatlt : pat < (strides kk).2 := by
      rw [(strides_spec kk).2.1, hkksize, hpat]
      exact sum_lt_sprod kk _ iS (fun i hi => by rw [hkkget i hi]; exact min_le_right _ _)
    obtain ⟨hF, hPr, hProf⟩ := patternData_spec Sq kk Bq cd N1 (strides kk).2 hpatlt
    have hcF : c.patF[pat]! = sumCd cd (smallDivs Sq kk N1 pat) := hF
    set a' := (patternData Sq kk Bq cd N1 (strides kk).2).2.2[
      (patternData Sq kk Bq cd N1 (strides kk).2).2.1[pat]!]! with ha'_def
    have hctab : c.tabs[c.patProf[pat]!]! = buildTab a' Bq Bdn ((Array.range Bq.size).map
        fun i => pmArr Bq[i]! Bdn[i]! (P.KH - 1)) H.D P.KH (dn * (p - 1) / DDEN) := by
      show ((patternData Sq kk Bq cd N1 (strides kk).2).2.2.map fun a => buildTab a Bq Bdn
        ((Array.range Bq.size).map fun i => pmArr Bq[i]! Bdn[i]! (P.KH - 1)) H.D P.KH
          (dn * (p - 1) / DDEN))[(patternData Sq kk Bq cd N1 (strides kk).2).2.1[pat]!]! = _
      rw [getElem!_map _ _ hPr]
    -- the profile is `a_q(s_S(u))`
    have hsm0 : smooth S u ≠ 0 := smooth_ne_zero (fun q hq => (idxSet_prime hq).pos) u
    have hBqpos : ∀ q ∈ Bq.toList, 0 < q := fun q hq => (hBqmem q hq).1.pos
    have hprof : ∀ q, profileFn Bq a' q = A.sbhProfile p P.m B (smooth S u) q := by
      intro q
      rw [hProf, profileFn_profileOf (m := P.m) (p := p) (by omega) hBqpos hsm0 hnd hmem q]
      unfold A.sbhProfile
      rw [hBset]
    have hprofF : profileFn Bq a' = A.sbhProfile p P.m B (smooth S u) := funext hprof
    -- the table (L2-C's `buildTab_sound`)
    have hBdn : Bdn = Bq.map (deltaN2 P) := by rw [hBdn_def, hBq_def]; exact dns2_extract P iS iB
    have ha'size : a'.size = Bq.size := by rw [hProf, profileOf_size]
    obtain ⟨hbm, hEb, hrows⟩ := hBT P hPX hH (Bq := Bq) (Bdn := Bdn) (a := a') hBqmem hBqnd
      (by rw [hHset, hBset]; exact hBH) hBdn ha'size (dn * (p - 1) / DDEN) N (by omega)
    set tab := buildTab a' Bq Bdn ((Array.range Bq.size).map fun i => pmArr Bq[i]! Bdn[i]!
      (P.KH - 1)) H.D P.KH (dn * (p - 1) / DDEN) with htab_def
    have hsumB : ∑ q ∈ B ∪ Hs, A.sbhProfile p P.m B (smooth S u) q =
        ∑ q ∈ Bq.toList.toFinset, profileFn Bq a' q := by
      rw [sum_union hBH, ← hBset, hprofF]
      have : ∑ q ∈ Hs, A.sbhProfile p P.m B (smooth S u) q = 0 := sum_eq_zero fun q hq => by
        unfold A.sbhProfile
        rw [ite_eq_right (fun h => Finset.disjoint_left.1 hBH h hq)]
      rw [hBset, this, add_zero]
    have htabok : TabOK (B ∪ Hs) (nu2 P) N (A.sbhProfile p P.m B (smooth S u)) tab := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hsumB, sum_profileFn hBqnd ha'size, ← hbm]
      · rw [A.expect_bstat (fun q _ => by omega) _ (nu2 P)]
        refine hEb.trans (le_of_eq ?_)
        rw [sum_union hBH, ← hBset, hprofF]
        have : ∑ q ∈ Hs, (A.sbhProfile p P.m B (smooth S u) q : ℝ) * (nu2 P q / q) = 0 :=
          sum_eq_zero fun q hq => by
            unfold A.sbhProfile
            rw [ite_eq_right (fun h => Finset.disjoint_left.1 hBH h hq)]
            simp
        rw [hBset, this, add_zero]
      · intro b hb cc hc hK
        have := hrows b hb cc hc hK
        rw [hHset, hBset, hprofF] at this
        exact this
    -- the leaf bound
    have hET' : expect (B ∪ Hs) (nu2 P) (fun _ => N) (fun w => (tauN (B ∪ Hs) w : ℝ)) ≤
        wv c.ETW :=
      (expect_tauN_le hR1 (fun q hq => (hνR q hq).1) _).trans
        (hprodR.trans (pv_le_wv_cdiv ET))
    have hβ : wv (c.tp1 + c.patF[pat]!) ≤
        Fsum p P.m (smooth S u) + delta2 P p * ((p : ℝ) - 1) := by
      rw [wv_add, hcF]
      have h1 : wv c.tp1 ≤ (dn : ℝ) / 10 ^ 9 * ((p : ℝ) - 1) :=
        wv_tp1_le dn p (by omega)
      have h2 := sumCd_le_Fsum (m := P.m) (p := p) (by omega) hsm0 hnd hmem
      rw [hδp]
      linarith
    have hω : wv c.om ≤ 1 - 1 / (p : ℝ) := wv_om_le (by omega)
    have hGlv : G u ≤ wv (leafValue c.tabs[c.patProf[pat]!]! c.patF[pat]! τ c.ETW c.tp1 c.om
        c.omP).1 := by
      rw [hctab] at hlv ⊢
      exact leafValue_sound hνR htabok (tauN_pos S u) hET' hβ hω hlv
    unfold accW
    simp only
    rw [show acc.leaf + mulUp P' (leafValue c.tabs[c.patProf[pat]!]! c.patF[pat]! τ c.ETW c.tp1
        c.om c.omP).1 + acc.prune = (acc.leaf + acc.prune) + mulUp P' (leafValue
        c.tabs[c.patProf[pat]!]! c.patF[pat]! τ c.ETW c.tp1 c.om c.omP).1 by ring,
      wv_add (acc.leaf + acc.prune)]
    have h1 := pv_mul_wv_le_mulUp P' (leafValue c.tabs[c.patProf[pat]!]! c.patF[pat]! τ c.ETW
      c.tp1 c.om c.omP).1
    have h2 := mul_le_mul_of_nonneg_left hGlv (pv_nonneg' P')
    linarith [h2.trans h1]
  have key := dfs_nodeVal c (fun i => (primes2 P)[i]!) iS N (nu2 P) G
    (fun i => kkOf (primes2 P)[i]! N1) (fun i => sprod kk i) (pv ET) hc_nS
    (fun i hi j hj h => primes2_inj (by simp at hi; omega) (by simp at hj; omega) h)
    (fun i hi => (primes2_prime (by omega)).one_lt)
    (fun i hi => hνpr _ (primes2_prime (by omega)) ((primes2_le (by omega)).trans hPX))
    hG0 (pv_nonneg' ET) (by rw [hsuf]; exact hG)
    (fun j hj => by
      rw [hc_acut j hj]
      have := C.acut60_le (two_le_primes2 (P := P) (i := j) (by omega))
      omega)
    hc_kk hc_stride
    (fun j hj a ha => by
      rw [hc_pm j hj]
      rw [hc_acut j hj] at ha
      have := C.acut60_le (two_le_primes2 (P := P) (i := j) (by omega))
      exact C.rho_nu2_le_pmArr (two_le_primes2 (by omega)) ((primes2_le (by omega)).trans hPX) ha
        (by omega))
    (fun j hj a ha => by
      rw [hc_h j hj]
      rw [hc_acut j hj] at ha
      exact C.hMass_nu2_le_hArr (two_le_primes2 (by omega)) ((primes2_le (by omega)).trans hPX)
        ha N)
    (fun j hj => by
      rw [hc_REW j hj, sufSet_eq_idxSet hiSsize (j + 1)]
      have h1 := prodUp_ge (fun i => facE1u Sq[i]! Sdn[i]!) (Sq.size - (j + 1)) ONE2 (j + 1)
      rw [pv_ONE2', one_mul] at h1
      have h2 := prod_facE1u_ge (P := P) (a := 0) (b := iS) hPX (Nat.zero_le _) hiSsize
        (i := j + 1) (len := Sq.size - (j + 1)) (by omega)
      rw [show 0 + (j + 1) + (Sq.size - (j + 1)) = iS by omega,
        show 0 + (j + 1) = j + 1 by omega, ← hSq_def, ← hSdn_def] at h2
      have h3 := pv_mul_pv_le_REW
        (prodUp (fun i => facE1u Sq[i]! Sdn[i]!) ONE2 (j + 1) (Sq.size - (j + 1))) ET
      calc pv ET * ∏ q ∈ idxSet P (j + 1) iS, (1 + nu2 P q / ((q : ℝ) - 1))
          ≤ pv ET * pv (prodUp (fun i => facE1u Sq[i]! Sdn[i]!) ONE2 (j + 1)
              (Sq.size - (j + 1))) := mul_le_mul_of_nonneg_left (h2.trans h1) (pv_nonneg' _)
        _ = pv (prodUp (fun i => facE1u Sq[i]! Sdn[i]!) ONE2 (j + 1) (Sq.size - (j + 1))) *
              pv ET := mul_comm _ _
        _ ≤ _ := h3)
    hleaf 100000 haccok
  rw [hsuf] at key
  exact key


/-- `BuildTabSpec` holds: L2-C's `C.buildTab_sound` (`Checker2Sound/Tables.lean`). -/
theorem buildTabSpec_holds : BuildTabSpec := by
  intro P hPX H hH Bq Bdn a hBq hBnd hBH hBdn ha tp1int N hN
  exact C.buildTab_sound P hPX hH hBq hBnd hBH hBdn ha tp1int N hN

/-- **(L2-D) `sbhCost_sound`** — exactly the statement of `Checker2Sound/Interfaces.lean`:
soundness of the S/B/H cost at the prime `p = primes2 P [k]` with `N1 ≥ 3`, given a valid `T_H`
state, for every cap `N`. -/
theorem sbhCost_sound (P : Params2) (hPX : P.PX ≤ P.X) {k : ℕ} (hk : k < (primes2 P).size)
    (hN1 : 3 ≤ cdiv P.m (primes2 P)[k]!) {H : HState} (hH : HValid P H)
    (hok : (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).ok = true) (N : ℕ) :
    hingeLoss P.m (delta2 P) (primes2 P)[k]! (fun _ => N) ≤
      pv (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).cost :=
  sbhCost_sound_of buildTabSpec_holds P hPX hk hN1 hH hok N

end MinModulus.Checker2Sound.D
