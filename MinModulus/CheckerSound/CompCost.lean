import MinModulus.CheckerSound.CompCostEnum
import MinModulus.CheckerSound.CompCostRem
import MinModulus.CheckerSound.TauDP

/-!
# `CheckerSound.CompCost` (agent CS-C): soundness of `comparisonCost`

Status: complete, no `sorry`.

**`comparisonCost_sound`** (the statement of `CheckerSound/Interfaces.lean`, verbatim): for a
prime `p ≤ X` with `δ_p = deltaN P p / 10^9 > 0`, the A-primes `aps` = the primes below `z`
(increasing), `adns = aps.map (deltaN P)`, a valid A-part state `A` for them and a valid B-part
state `B` for the primes in `[z, p)`, if the run-time guard `ok` holds then
`hingeLoss P.m (delta0 P) p (fun _ => N) ≤ pv cost` for **every** uniform cap `N`.

Proof: `CheckerMath.hingeLoss_le_of_comparison` with `ν := tilt (delta0 P)` (exact tilts),
`N0 = 65`, `E = {v | s_A(v) ≤ X_p}`, `KM = KMAX`, `acut = acutA P`,
`R_k = pv (up[k] - pen[k])` (`restMass_eq`, `AValid.law`, and `pen[k] ≤ enumMass k` from the
enumeration semantics), `LA = pv tailA` (`AValid.lost`), `EB = pv B.EB` (CS-B's
`BValid_meanTau_le`); then the three parts of the cost:
* the enumerated configurations: `enum_part_le` (`lin1 + lin2 + fbsum`), using the enumeration
  semantics `runEnum_view` (`EnumSem.lean`), the leaf probabilities `leaf_prob_bounds`
  (`EnumPat.lean`), `U_A = I/(pj1 (p-1))` (`thresholds_spec`) and CS-B's `BValid_gUp_ge`;
* the rest `Σ_k R_k G(k/(p-1), k/(p-1))`: `rem_part_le` (`remlin + remfb`, CS-B's
  `BValid_gUp_diag_ge`);
* the lost mass `LA·EB/(p-1)`: `pv_tail_ge`; the division by `1 - δ_p`: `pv_cost_ge`.
-/

namespace MinModulus.CheckerSound.C

open MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Smooth MinModulus.Main Finset

/-! ### The array of A-primes -/

section
variable {aps : Array ℕ} {z : ℕ}

theorem getElem!_eq_getElem (aps : Array ℕ) {j : ℕ} (hj : j < aps.size) : aps[j]! = aps[j] := by
  rw [← getD0_eq_getElem!, getD0_eq, Array.getElem?_eq_getElem hj]
  rfl

theorem aps_mem (haps : aps.toList = (List.range z).filter (fun q => decide q.Prime)) {j : ℕ}
    (hj : j < aps.size) : aps[j]! ∈ Nat.primesBelow z := by
  have hmem : aps[j] ∈ aps.toList := Array.getElem_mem_toList hj
  rw [haps, List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
  rw [getElem!_eq_getElem aps hj, Nat.mem_primesBelow]
  exact hmem

theorem aps_lt (haps : aps.toList = (List.range z).filter (fun q => decide q.Prime)) {j j' : ℕ}
    (hjj' : j < j') (hj' : j' < aps.size) : aps[j]! < aps[j']! := by
  have hpw : aps.toList.Pairwise (· < ·) := by
    rw [haps]
    exact (List.pairwise_lt_range (n := z)).filter _
  rw [getElem!_eq_getElem aps (by omega), getElem!_eq_getElem aps hj', ← Array.getElem_toList,
    ← Array.getElem_toList]
  exact List.pairwise_iff_getElem.1 hpw j j' (by simp; omega) (by simp; omega) hjj'

theorem aps_image (haps : aps.toList = (List.range z).filter (fun q => decide q.Prime)) :
    (Ico 0 aps.size).image (fun j => getD0 aps j) = Nat.primesBelow z := by
  ext q
  simp only [mem_image, mem_Ico, Nat.mem_primesBelow]
  constructor
  · rintro ⟨j, ⟨-, hj⟩, rfl⟩
    rw [getD0_eq_getElem!]
    exact Nat.mem_primesBelow.1 (aps_mem haps hj)
  · rintro ⟨hqz, hq⟩
    have hmem : q ∈ aps.toList := by
      rw [haps, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨hqz, hq⟩
    obtain ⟨j, hj, hjq⟩ := List.getElem_of_mem hmem
    rw [Array.length_toList] at hj
    refine ⟨j, ⟨Nat.zero_le j, hj⟩, ?_⟩
    rw [getD0_eq_getElem!, getElem!_eq_getElem aps hj, ← Array.getElem_toList]
    exact hjq

end

theorem getElem!_map_of_lt (aps : Array ℕ) (f : ℕ → ℕ) {j : ℕ} (hj : j < aps.size) :
    (aps.map f)[j]! = f aps[j]! := by
  rw [getElem!_eq_getElem _ (by simpa using hj), getElem!_eq_getElem aps hj, Array.getElem_map]

/-! ### Exponent bounds below `2^62` -/

theorem exp_le_62 {q b : ℕ} (hq : 2 ≤ q) (h : q ^ b ≤ 2 ^ 62) : b ≤ 62 := by
  by_contra hb
  have h1 : 2 ^ 63 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ b ≤ q ^ b := Nat.pow_le_pow_left hq b
  have : (2 : ℕ) ^ 62 < 2 ^ 63 := by norm_num
  omega

theorem pow_le_smooth {S : Finset ℕ} (hS : ∀ q ∈ S, 0 < q) (w : ℕ → ℕ) {q : ℕ} (hq : q ∈ S) :
    q ^ w q ≤ smooth S w :=
  Nat.le_of_dvd (smooth_pos hS w) (dvd_prod_of_mem (fun r => r ^ w r) hq)

/-! ### The enumerated mass at `τ = k` -/

section
variable {cfg : EnumCfg}

/-- `pen[k] ≤ Σ_{w enumerated, τ(w) = k} π(w)` (P-values; `k ≤ KMAX`). -/
theorem pen_le_enumMass {adns : Array ℕ} (h : EnumHyp cfg) (hP : PatHyp cfg adns) {N : ℕ}
    (hγ : CapOK cfg (fun _ => N)) (hγ' : ∀ w ∈ L cfg (fun _ => N) 0 1, ∀ q ∈ Ps cfg 0, w q < N)
    (hX1 : 1 ≤ cfg.X) {bufSize : ℕ} (hok : (runEnum cfg bufSize).ok = true) {ν : ℕ → ℝ}
    (hν : ∀ j < cfg.aps.size, ν (qf cfg j) = (DDEN : ℝ) / ((DDEN : ℝ) - (adns[j]! : ℝ)))
    (hd : ∀ j < cfg.aps.size, 2 * adns[j]! ≤ DDEN) {k : ℕ} (hk : k ≤ cfg.kmax) :
    pv (getD0 (runEnum cfg bufSize).pen k) ≤
      ∑ w ∈ L cfg (fun _ => N) 0 1, weight (Ps cfg 0) ν (fun _ => N) w *
        (if (smooth (Ps cfg 0) w).divisors.card = k then 1 else 0) := by
  have hview := runEnum_view h hγ hX1 bufSize hok
  have hpen : getD0 (runEnum cfg bufSize).pen k = ∑ w ∈ L cfg (fun _ => N) 0 1,
      (if τW cfg w ≤ cfg.kmax ∧ k = τW cfg w then plW cfg w else 0) :=
    view_eq_sum hview 0 k
  rw [hpen, pv_sum]
  refine sum_le_sum fun w hw => ?_
  by_cases hτ : τW cfg w = k
  · have hc : τW cfg w ≤ cfg.kmax ∧ k = τW cfg w := ⟨hτ ▸ hk, hτ.symm⟩
    rw [ite_eq_left hc]
    have : (smooth (Ps cfg 0) w).divisors.card = k := hτ
    rw [ite_eq_left this, mul_one]
    exact (leaf_prob_bounds h hP ν hν hd (hγ' w hw)).1
  · have hc : ¬ (τW cfg w ≤ cfg.kmax ∧ k = τW cfg w) := fun hc => hτ hc.2.symm
    rw [ite_eq_right hc, pv_zero]
    have : ¬ (smooth (Ps cfg 0) w).divisors.card = k := hτ
    rw [ite_eq_right this, mul_zero]

end

/-! ### Soundness of `comparisonCost` -/

set_option linter.unusedVariables false in
/-- **(CS-C, Interfaces)** Soundness of `comparisonCost` at a prime `p ≤ X` with
`δ_p = deltaN P p/10^9 > 0`, for the partition of the primes below `p` into `A` = the primes
below `z` (the array `aps`, in increasing order, with δ-values `adns`) and `B` = the primes in
`[z, p)`: if the run-time guard `ok` holds, the cost bounds the hinge loss for every uniform cap
`N`. (The hypothesis `hdn : δ_p > 0` of the interface is not needed.) -/
theorem comparisonCost_sound (P : Params) {p : ℕ} (hp : p.Prime) (hpX : p ≤ P.PMAX)
    (hdn : 0 < deltaN P p) {z : ℕ} (hzp : z ≤ p) (aps adns : Array ℕ)
    (haps : aps.toList = (List.range z).filter (fun q => decide q.Prime))
    (hadns : adns = aps.map (deltaN P)) {A : AState} (hA : AValid P A (Nat.primesBelow z))
    {B : BState} (hB : BValid P B ((Nat.primesBelow p).filter (z ≤ ·)))
    (hok : (comparisonCost P p (deltaN P p) aps adns A B).ok = true) (N : ℕ) :
    hingeLoss P.m (delta0 P) p (fun _ => N) ≤
      pv (comparisonCost P p (deltaN P p) aps adns A B).cost := by
  have hp2 : 2 ≤ p := hp.two_le
  have hdnD : deltaN P p < DDEN := MinModulus.CheckerSound.B.deltaN_lt_DDEN P p
  have hδp : delta0 P p = (deltaN P p : ℝ) / 10 ^ 9 := delta0_of_le hpX
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  -- unfold the code
  unfold comparisonCost at hok ⊢
  generalize hth : thresholds P.m p = th at hok ⊢
  obtain ⟨J, M1, M2, pj1, pj2⟩ := th
  dsimp only at hok ⊢
  generalize hfbt : fbTable B.D (deltaN P p * (p - 1) / DDEN + 2) = fbt at hok ⊢
  obtain ⟨S0, PP⟩ := fbt
  generalize hpc : patternConsts aps adns = pc at hok ⊢
  obtain ⟨bits, cup, clo⟩ := pc
  dsimp only at hok ⊢
  obtain ⟨cfg, hcfg⟩ : ∃ cfg : EnumCfg, cfg =
      { aps := aps, bits := bits, X := enumCutoff P p, M1 := M1, M2 := M2, pj1 := pj1, pj2 := pj2,
        It := cdiv (deltaN P p * (pj1 * (p - 1))) DDEN,
        n1max := cdiv (cdiv (deltaN P p * (pj1 * (p - 1))) DDEN) pj1 + 1, cup := cup, clo := clo,
        kmax := P.KMAX } := ⟨_, rfl⟩
  rw [← hcfg] at hok ⊢
  generalize hrem : comparisonCost.remaining p (deltaN P p) (fun cP => fbUp B.EB B.lost S0 PP cP)
    (pj1 * (p - 1)) A.up (runEnum cfg M1).pen 1 0 0 0 (min P.KMAX A.kTop) = rem
  obtain ⟨rs0, rs1, remfb⟩ := rem
  dsimp only
  -- the run-time guards
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hokE, hK⟩, hJ⟩, hXle⟩ := hok
  -- the fields of the enumeration configuration
  have cA : cfg.aps = aps := by rw [hcfg]
  have cB : cfg.bits = bits := by rw [hcfg]
  have cX : cfg.X = enumCutoff P p := by rw [hcfg]
  have cM1 : cfg.M1 = M1 := by rw [hcfg]
  have cM2 : cfg.M2 = M2 := by rw [hcfg]
  have cpj1 : cfg.pj1 = pj1 := by rw [hcfg]
  have cpj2 : cfg.pj2 = pj2 := by rw [hcfg]
  have cIt : cfg.It = cdiv (deltaN P p * (cfg.pj1 * (p - 1))) DDEN := by rw [hcfg]
  have cup' : cfg.cup = cup := by rw [hcfg]
  have clo' : cfg.clo = clo := by rw [hcfg]
  have ckmax : cfg.kmax = P.KMAX := by rw [hcfg]
  -- thresholds
  obtain ⟨hM2, hM21, hpj1, hU⟩ := thresholds_spec hp2 hth hJ
  -- the A-primes
  have hq_mem : ∀ j < cfg.aps.size, qf cfg j ∈ Nat.primesBelow z := by
    intro j hj
    rw [cA] at hj
    unfold qf
    rw [cA, getD0_eq_getElem!]
    exact aps_mem haps hj
  have hPs : Ps cfg 0 = Nat.primesBelow z := by
    unfold Ps qf
    rw [cA]
    exact aps_image haps
  have hAprime : ∀ q ∈ Nat.primesBelow z, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
  have hEH : EnumHyp cfg := by
    refine ⟨fun j hj => hAprime _ (hq_mem j hj), fun j j' hjj' hj' => ?_, by rw [cM1, cM2]; exact hM21⟩
    rw [cA] at hj'
    unfold qf
    rw [cA, getD0_eq_getElem!, getD0_eq_getElem!]
    exact aps_lt haps hjj' hj'
  have hPH : PatHyp cfg adns := ⟨by rw [cB, cA, hpc], by rw [cup', cA, hpc], by rw [clo', cA, hpc]⟩
  have hadns_j : ∀ j < cfg.aps.size, adns[j]! = deltaN P (qf cfg j) := by
    intro j hj
    rw [cA] at hj
    unfold qf
    rw [cA, hadns, getElem!_map_of_lt aps (deltaN P) hj, getD0_eq_getElem!]
  have hν : ∀ j < cfg.aps.size, tilt (delta0 P) (qf cfg j) =
      (DDEN : ℝ) / ((DDEN : ℝ) - (adns[j]! : ℝ)) := by
    intro j hj
    have hqz := Nat.mem_primesBelow.1 (hq_mem j hj)
    rw [tilt_delta0_of_le (by omega), hadns_j j hj, cast_DDEN]
  have hd : ∀ j < cfg.aps.size, 2 * adns[j]! ≤ DDEN := by
    intro j hj
    rw [hadns_j j hj]
    exact MinModulus.CheckerSound.B.two_mul_deltaN_le_DDEN P _
  have hXle' : cfg.X ≤ 2 ^ 62 := by rw [cX]; exact hXle
  have hX1 : 1 ≤ cfg.X := by rw [cX]; unfold enumCutoff; omega
  -- the partition of the primes below `p`
  have hAB : Nat.primesBelow z ∪ (Nat.primesBelow p).filter (z ≤ ·) = Nat.primesBelow p := by
    ext q
    simp only [mem_union, mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, -⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      by_cases hqz : q < z
      · exact Or.inl ⟨hqz, h2⟩
      · exact Or.inr ⟨⟨h1, h2⟩, by omega⟩
  have hdisj : Disjoint (Nat.primesBelow z) ((Nat.primesBelow p).filter (z ≤ ·)) := by
    rw [disjoint_left]
    intro q hq hq'
    rw [mem_filter] at hq'
    have := (Nat.mem_primesBelow.1 hq).1
    omega
  -- the comparison bound, every cap
  refine hingeLoss_le_of_comparison hp (fun q _ => delta0_nonneg P q)
    (fun q _ => delta0_le_half P q) (ν := tilt (delta0 P))
    (fun q hq => ⟨le_rfl, (tilt_mem (fun q _ => delta0_nonneg P q) (fun q _ => delta0_le_half P q)
      (Nat.prime_of_mem_primesBelow hq)).2⟩) hAB hdisj
    (fun a => smooth (Nat.primesBelow z) a ≤ enumCutoff P p) P.KMAX (acutA P) 65 _ ?_ N
  intro N hN
  -- the caps are above every enumerated exponent
  have hγ : CapOK cfg (fun _ => N) := by
    intro j hj b hb
    show b ≤ N
    have := exp_le_62 (hAprime _ (hq_mem j hj)).two_le (hb.trans hXle')
    omega
  have hγ' : ∀ w ∈ L cfg (fun _ => N) 0 1, ∀ q ∈ Ps cfg 0, w q < N := by
    intro w hw q hq
    have hwX : 1 * smooth (Ps cfg 0) w ≤ cfg.X := (mem_filter.1 hw).2
    have h1 := pow_le_smooth (pos_of_mem_Ps hEH) w hq
    have := exp_le_62 (prime_of_mem_Ps hEH hq).two_le (h1.trans (by omega))
    omega
  have hνS : ∀ q ∈ (Nat.primesBelow p).filter (z ≤ ·), 0 ≤ tilt (delta0 P) q ∧ tilt (delta0 P) q ≤ q :=
    MinModulus.CheckerSound.B.BValid_tilt_mem hB
  -- the enumerated configurations are `E`
  have hLE : L cfg (fun _ => N) 0 1 =
      (box (Nat.primesBelow z) (fun _ => N)).filter
        (fun a => smooth (Nat.primesBelow z) a ≤ enumCutoff P p) := by
    unfold L
    rw [hPs, cX]
    exact filter_congr fun w _ => by rw [Nat.one_mul]
  refine ⟨fun k => pv (A.up[k]! - getD0 (runEnum cfg M1).pen k), pv A.tailA, pv B.EB,
    fun k hk => ?_, hA.lost N hN, MinModulus.CheckerSound.B.BValid_meanTau_le hB _, ?_⟩
  · -- the non-enumerated kept mass `R_k`
    have hE : ∀ a ∈ box (Nat.primesBelow z) (fun _ => N),
        smooth (Nat.primesBelow z) a ≤ enumCutoff P p → tauN (Nat.primesBelow z) a ≤ P.KMAX →
          ∀ q ∈ Nat.primesBelow z, a q ≤ acutA P q := by
      intro a _ ha _ q hq
      by_contra hc
      have h1 : q ^ (acutA P q + 1) ≤ q ^ a q :=
        Nat.pow_le_pow_right (hAprime q hq).pos (by omega)
      have h2 := pow_le_smooth (fun r hr => (hAprime r hr).pos) a hq
      have h3 := hA.acut q hq
      omega
    rw [restMass_eq hE hk]
    have hlaw := hA.law N hN k hk
    have hpen := pen_le_enumMass hEH hPH hγ hγ' hX1 hokE hν hd (k := k) (by rw [ckmax]; exact hk)
    have hmass : ∑ w ∈ L cfg (fun _ => N) 0 1, weight (Ps cfg 0) (tilt (delta0 P)) (fun _ => N) w *
          (if (smooth (Ps cfg 0) w).divisors.card = k then 1 else 0) =
        enumMass (Nat.primesBelow z) (tilt (delta0 P)) (fun _ => N)
          (fun a => smooth (Nat.primesBelow z) a ≤ enumCutoff P p) k := by
      unfold enumMass
      rw [hLE, hPs]
      refine sum_congr rfl fun w _ => ?_
      rw [card_divisors_smooth_eq_tauN hAprime]
    rw [hmass] at hpen
    have := pv_sub_ge (A.up[k]!) (getD0 (runEnum cfg M1).pen k)
    linarith
  · -- the three parts of the cost
    rw [hδp]
    have hEB := MinModulus.CheckerSound.B.BValid_meanTau_le hB (fun _ => N)
    -- enumerated configurations
    have h1 := enum_part_le (m := P.m) hEH hPH hγ hγ' hX1 hokE hν hd hνS hp2 (by rw [cpj1]; exact hpj1)
      (by rw [cM1, cM2]; exact ⟨hM2, hM21⟩) (by rw [cpj1, cpj2, cM1, cM2]; exact hU) cIt hEB
      (fb := fun cP => fbUp B.EB B.lost S0 PP cP)
      (fun τ uNum uDen hτ huDen hut => MinModulus.CheckerSound.B.BValid_gUp_ge hB hK hfbt hN hp2
        hτ huDen hut le_rfl le_rfl)
    rw [cpj1, cpj2] at h1
    have hsumE : ∑ a ∈ (box (Nat.primesBelow z) (fun _ => N)).filter
          (fun a => smooth (Nat.primesBelow z) a ≤ enumCutoff P p),
          weight (Nat.primesBelow z) (tilt (delta0 P)) (fun _ => N) a *
            GB ((Nat.primesBelow p).filter (z ≤ ·)) (tilt (delta0 P)) (fun _ => N)
              ((deltaN P p : ℝ) / 10 ^ 9)
              ((tauN (Nat.primesBelow z) a : ℝ) / ((p : ℝ) - 1))
              (Up p P.m (smooth (Nat.primesBelow z) a)) =
        ∑ w ∈ L cfg (fun _ => N) 0 1, weight (Ps cfg 0) (tilt (delta0 P)) (fun _ => N) w *
          GB ((Nat.primesBelow p).filter (z ≤ ·)) (tilt (delta0 P)) (fun _ => N)
            ((deltaN P p : ℝ) / 10 ^ 9)
            (((smooth (Ps cfg 0) w).divisors.card : ℝ) / ((p : ℝ) - 1))
            (Up p P.m (smooth (Ps cfg 0) w)) := by
      rw [hLE, hPs]
      refine sum_congr rfl fun w _ => ?_
      rw [card_divisors_smooth_eq_tauN hAprime]
    -- the rest
    have h2 := rem_part_le hνS hp2 A.up (runEnum cfg M1).pen hA.top hEB
      (fb := fun cP => fbUp B.EB B.lost S0 PP cP)
      (fun k hk hkt => MinModulus.CheckerSound.B.BValid_gUp_diag_ge hB hK hfbt hN hp2 hk hkt) hrem
    -- the lost mass
    have h3 := pv_tail_ge A.tailA B.EB p hp2
    -- the division by `1 - t`
    refine le_trans (div_le_div_of_nonneg_right ?_ (by
      have : (deltaN P p : ℝ) < 10 ^ 9 := by
        have := hdnD; rw [show DDEN = 10 ^ 9 from rfl] at this; exact_mod_cast this
      have : (deltaN P p : ℝ) / 10 ^ 9 < 1 := by rw [div_lt_one (by norm_num)]; exact this
      linarith)) (pv_cost_ge _ _ hdnD)
    simp only [pv_add]
    rw [hsumE]
    linarith

end MinModulus.CheckerSound.C
