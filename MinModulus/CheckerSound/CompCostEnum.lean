import MinModulus.CheckerSound.CompCostLoops

/-!
# `CheckerSound.CompCostEnum` (agent CS-C): the enumerated part of `comparisonCost`

Status: complete, no `sorry`.

**`enum_part_le`**: for the enumeration configuration of `comparisonCost` (A-primes increasing,
`patternConsts`, thresholds with `J ≤ 3`, caps `N` above every fitting exponent) and a run with
`ok = true`,
`Σ_{w : s(w) ≤ X} π(w) G(τ(w)/(p-1), U_p(s(w))) ≤ pv lin1 + pv lin2 + pv fbsum`,
where `lin1`, `lin2`, `fbsum` are the code's expressions built from the arrays `hn`, `hs1`,
`hs2`, `fb` of `runEnum`. The linear leaves (`I ≥ It`, i.e. `U ≥ t`) use
`CheckerMath.sum_GB_linear_le` and the histogram sums; the other leaves use the `gUp` bound
(hypothesis `hG`, discharged by CS-B's `BValid_gUp_ge`) at the decoded key (`key_decode`).
-/

namespace MinModulus.CheckerSound.C

open MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Smooth Finset

/-! ### Leaf quantities of a configuration `w` -/

section
variable (cfg : EnumCfg)

/-- `s(w)`. -/
def sW (w : ℕ → ℕ) : ℕ := smooth (Ps cfg 0) w
/-- `τ(s(w))`. -/
def τW (w : ℕ → ℕ) : ℕ := (sW cfg w).divisors.card
/-- `σ₁(s(w))`. -/
def σ1W (w : ℕ → ℕ) : ℕ := sig cfg.M1 (sW cfg w)
/-- `σ₂(s(w))`. -/
def σ2W (w : ℕ → ℕ) : ℕ := sig cfg.M2 (sW cfg w)
/-- `I(w) = pj1 (τ - σ₁) + pj2 (σ₁ - σ₂) + σ₂`. -/
def IW (w : ℕ → ℕ) : ℕ := cfg.pj1 * (τW cfg w - σ1W cfg w) + cfg.pj2 * (σ1W cfg w - σ2W cfg w) + σ2W cfg w
/-- `⌈cup[pat]/s⌉`. -/
def puW (w : ℕ → ℕ) : ℕ := cdiv (getD0 cfg.cup (patOf cfg 0 w)) (sW cfg w)
/-- `⌊clo[pat]/s⌋`. -/
def plW (w : ℕ → ℕ) : ℕ := getD0 cfg.clo (patOf cfg 0 w) / sW cfg w
/-- The `fb` index `(n1·M1 + σ₁)·M2 + σ₂`. -/
def keyW (w : ℕ → ℕ) : ℕ := ((τW cfg w - σ1W cfg w) * cfg.M1 + σ1W cfg w) * cfg.M2 + σ2W cfg w

end

section
variable {cfg : EnumCfg}

theorem view_eq_sum {γ : ℕ → ℕ} {acc : EnumAcc}
    (hview : view acc = ∑ w ∈ L cfg γ 0 1, LV cfg (smooth (Ps cfg 0) w) (patOf cfg 0 w))
    (k : Fin 5) (j : ℕ) :
    view acc k j = ∑ w ∈ L cfg γ 0 1, LV cfg (smooth (Ps cfg 0) w) (patOf cfg 0 w) k j := by
  rw [hview, Finset.sum_apply, Finset.sum_apply]

theorem sW_pos (h : EnumHyp cfg) (w : ℕ → ℕ) : 0 < sW cfg w := smooth_pos (pos_of_mem_Ps h) w

theorem one_le_τW (h : EnumHyp cfg) (w : ℕ → ℕ) : 1 ≤ τW cfg w := by
  unfold τW
  exact card_pos.2 ⟨1, Nat.mem_divisors.2 ⟨one_dvd _, (sW_pos h w).ne'⟩⟩

theorem σ_le (h : EnumHyp cfg) (w : ℕ → ℕ) : σ2W cfg w ≤ σ1W cfg w ∧ σ1W cfg w ≤ τW cfg w :=
  ⟨sig_mono h.M21 _, sig_le_card _ _⟩

end

/-! ### Rounded forms of `lin1`, `lin2` -/

theorem pv_lin1_ge (SPI SP dn uDen : ℕ) (huDen : 0 < uDen) :
    pv SPI / uDen - (dn : ℝ) / 10 ^ 9 * pv SP ≤
      pv (cdiv (SPI * DDEN - dn * uDen * SP) (DDEN * uDen)) := by
  have hu : (0 : ℝ) < (uDen : ℝ) := by exact_mod_cast huDen
  refine le_trans ?_ (pv_cdiv_ge (Nat.mul_pos (by unfold DDEN; omega) huDen))
  refine le_trans ?_ (div_le_div_of_nonneg_right (pv_sub_ge _ _) (by positivity))
  have e : pv SPI / uDen - (dn : ℝ) / 10 ^ 9 * pv SP =
      (pv (SPI * DDEN) - pv (dn * uDen * SP)) / ((DDEN * uDen : ℕ) : ℝ) := by
    unfold pv
    push_cast
    rw [cast_DDEN]
    field_simp
  rw [e]

theorem pv_lin2_ge (EB S p : ℕ) (hp : 2 ≤ p) :
    (pv EB - 1) * (pv S / ((p : ℝ) - 1)) ≤ pv (cdiv ((EB - ONE) * S) ((p - 1) * ONE)) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hS : 0 ≤ pv S := pv_nonneg S
  have hEB : pv EB - 1 ≤ pv (EB - ONE) := by
    have := pv_sub_ge EB ONE
    rw [pv_ONE] at this
    exact this
  refine le_trans ?_ (pv_cdiv_ge (Nat.mul_pos (by omega) (by unfold ONE; omega)))
  have e : pv ((EB - ONE) * S) / (((p - 1) * ONE : ℕ) : ℝ) = pv (EB - ONE) * (pv S / ((p : ℝ) - 1)) := by
    have hc : (((p - 1) * ONE : ℕ) : ℝ) = ((p : ℝ) - 1) * 2 ^ 62 := by
      rw [Nat.cast_mul, cast_ONE, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
    rw [hc]
    generalize EB - ONE = a
    unfold pv
    rw [Nat.cast_mul]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right hEB (div_nonneg hS hp1.le)

/-! ### The enumerated part -/

section
variable {cfg : EnumCfg}

theorem enum_part_le {adns : Array ℕ} (h : EnumHyp cfg) (hP : PatHyp cfg adns) {N : ℕ}
    (hγ : CapOK cfg (fun _ => N)) (hγ' : ∀ w ∈ L cfg (fun _ => N) 0 1, ∀ q ∈ Ps cfg 0, w q < N)
    (hX1 : 1 ≤ cfg.X) {bufSize : ℕ} (hok : (runEnum cfg bufSize).ok = true) {ν : ℕ → ℝ}
    (hν : ∀ j < cfg.aps.size, ν (qf cfg j) = (DDEN : ℝ) / ((DDEN : ℝ) - (adns[j]! : ℝ)))
    (hd : ∀ j < cfg.aps.size, 2 * adns[j]! ≤ DDEN) {S : Finset ℕ}
    (hνS : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q) {p m dn : ℕ} (hp : 2 ≤ p) (hpj1 : 0 < cfg.pj1)
    (hM : 1 ≤ cfg.M2 ∧ cfg.M2 ≤ cfg.M1)
    (hU : ∀ s : ℕ, ((cfg.pj1 * (s.divisors.card - sig cfg.M1 s) +
        cfg.pj2 * (sig cfg.M1 s - sig cfg.M2 s) + sig cfg.M2 s : ℕ) : ℝ) /
          ((cfg.pj1 * (p - 1) : ℕ) : ℝ) = Up p m s)
    (hIt : cfg.It = cdiv (dn * (cfg.pj1 * (p - 1))) DDEN) {EB : ℕ}
    (hEB : meanTau S ν (fun _ => N) ≤ pv EB) {fb : ℕ → ℕ}
    (hG : ∀ τ uNum uDen : ℕ, 1 ≤ τ → 0 < uDen → uNum * DDEN ≤ dn * uDen →
      GB S ν (fun _ => N) ((dn : ℝ) / 10 ^ 9) ((τ : ℝ) / ((p : ℝ) - 1)) ((uNum : ℝ) / uDen) ≤
        pv (gUp fb dn p τ uNum uDen)) :
    ∑ w ∈ L cfg (fun _ => N) 0 1, weight (Ps cfg 0) ν (fun _ => N) w *
        GB S ν (fun _ => N) ((dn : ℝ) / 10 ^ 9)
          (((smooth (Ps cfg 0) w).divisors.card : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth (Ps cfg 0) w)) ≤
      pv (cdiv ((cfg.pj1 * weightedSum (runEnum cfg bufSize).hn +
            cfg.pj2 * weightedSum (runEnum cfg bufSize).hs1 + weightedSum (runEnum cfg bufSize).hs2 -
            cfg.pj2 * weightedSum (runEnum cfg bufSize).hs2) * DDEN -
          dn * (cfg.pj1 * (p - 1)) * arrSum (runEnum cfg bufSize).hn) (DDEN * (cfg.pj1 * (p - 1)))) +
      pv (cdiv ((EB - ONE) * (weightedSum (runEnum cfg bufSize).hn +
          weightedSum (runEnum cfg bufSize).hs1)) ((p - 1) * ONE)) +
      pv (comparisonCost.fbLeaves p dn fb cfg (cfg.pj1 * (p - 1)) (runEnum cfg bufSize).fb 0 0
          (runEnum cfg bufSize).fb.size) := by
  set acc := runEnum cfg bufSize with hacc
  set Lset := L cfg (fun _ => N) 0 1 with hLset
  set uDen := cfg.pj1 * (p - 1) with huDen
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have huDen0 : 0 < uDen := Nat.mul_pos hpj1 (by omega)
  have huDenR : (0 : ℝ) < (uDen : ℝ) := by exact_mod_cast huDen0
  set lin : (ℕ → ℕ) → Prop := fun w => cfg.It ≤ IW cfg w with hlin
  -- the arrays, from the enumeration semantics
  have hview := runEnum_view h hγ hX1 bufSize hok
  have hhn : ∀ j, getD0 acc.hn j =
      ∑ w ∈ Lset, if lin w ∧ j = τW cfg w - σ1W cfg w then puW cfg w else 0 :=
    fun j => view_eq_sum hview 1 j
  have hhs1 : ∀ j, getD0 acc.hs1 j = ∑ w ∈ Lset, if lin w ∧ j = σ1W cfg w then puW cfg w else 0 :=
    fun j => view_eq_sum hview 2 j
  have hhs2 : ∀ j, getD0 acc.hs2 j = ∑ w ∈ Lset, if lin w ∧ j = σ2W cfg w then puW cfg w else 0 :=
    fun j => view_eq_sum hview 3 j
  have hfbv : ∀ j, getD0 acc.fb j = ∑ w ∈ Lset, if ¬ lin w ∧ j = keyW cfg w then puW cfg w else 0 :=
    fun j => view_eq_sum hview 4 j
  -- histogram sums
  have hSP : arrSum acc.hn = ∑ w ∈ Lset.filter lin, puW cfg w := by
    rw [arrSum_eq]
    have := sum_getD0_mul acc.hn Lset lin (fun w => τW cfg w - σ1W cfg w) (puW cfg) hhn (fun _ => 1)
    simpa using this
  have hSN : weightedSum acc.hn = ∑ w ∈ Lset.filter lin, puW cfg w * (τW cfg w - σ1W cfg w) := by
    have := sum_getD0_mul acc.hn Lset lin (fun w => τW cfg w - σ1W cfg w) (puW cfg) hhn id
    simp only [id] at this
    rw [weightedSum_eq, ← this]
    exact sum_congr rfl fun j _ => Nat.mul_comm _ _
  have hS1 : weightedSum acc.hs1 = ∑ w ∈ Lset.filter lin, puW cfg w * σ1W cfg w := by
    have := sum_getD0_mul acc.hs1 Lset lin (σ1W cfg) (puW cfg) hhs1 id
    simp only [id] at this
    rw [weightedSum_eq, ← this]
    exact sum_congr rfl fun j _ => Nat.mul_comm _ _
  have hS2 : weightedSum acc.hs2 = ∑ w ∈ Lset.filter lin, puW cfg w * σ2W cfg w := by
    have := sum_getD0_mul acc.hs2 Lset lin (σ2W cfg) (puW cfg) hhs2 id
    simp only [id] at this
    rw [weightedSum_eq, ← this]
    exact sum_congr rfl fun j _ => Nat.mul_comm _ _
  have hFB := sum_getD0_mul acc.fb Lset (fun w => ¬ lin w) (keyW cfg) (puW cfg) hfbv
    (gKey cfg fb dn p uDen)
  -- per-leaf facts
  have hleaf : ∀ w ∈ Lset, weight (Ps cfg 0) ν (fun _ => N) w ≤ pv (puW cfg w) :=
    fun w hw => (leaf_prob_bounds h hP ν hν hd (hγ' w hw)).2
  have hUw : ∀ w, Up p m (smooth (Ps cfg 0) w) = (IW cfg w : ℝ) / uDen := fun w => (hU _).symm
  have hlinR : ∀ w, lin w ↔ (dn : ℝ) / 10 ^ 9 ≤ (IW cfg w : ℝ) / uDen := by
    intro w
    show cfg.It ≤ IW cfg w ↔ _
    rw [hIt]
    unfold cdiv
    rw [cdiv_le_iff_le_mul (by unfold DDEN; omega), div_le_div_iff₀ (by norm_num) huDenR]
    rw [← cast_DDEN]
    constructor
    · intro h1; exact_mod_cast (by linarith [h1] : dn * uDen ≤ IW cfg w * DDEN)
    · intro h1
      have : ((dn * uDen : ℕ) : ℝ) ≤ ((IW cfg w * DDEN : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  rw [← sum_filter_add_sum_filter_not Lset lin]
  -- the linear leaves
  have hL1 : ∑ w ∈ Lset.filter lin, weight (Ps cfg 0) ν (fun _ => N) w *
        GB S ν (fun _ => N) ((dn : ℝ) / 10 ^ 9)
          (((smooth (Ps cfg 0) w).divisors.card : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth (Ps cfg 0) w)) ≤
      pv (cdiv ((cfg.pj1 * weightedSum acc.hn + cfg.pj2 * weightedSum acc.hs1 +
            weightedSum acc.hs2 - cfg.pj2 * weightedSum acc.hs2) * DDEN -
          dn * uDen * arrSum acc.hn) (DDEN * uDen)) +
      pv (cdiv ((EB - ONE) * (weightedSum acc.hn + weightedSum acc.hs1)) ((p - 1) * ONE)) := by
    have step1 : ∑ w ∈ Lset.filter lin, weight (Ps cfg 0) ν (fun _ => N) w *
          GB S ν (fun _ => N) ((dn : ℝ) / 10 ^ 9)
            (((smooth (Ps cfg 0) w).divisors.card : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth (Ps cfg 0) w)) ≤
        ∑ w ∈ Lset.filter lin, pv (puW cfg w) *
          GB S ν (fun _ => N) ((dn : ℝ) / 10 ^ 9)
            ((τW cfg w : ℝ) / ((p : ℝ) - 1)) ((IW cfg w : ℝ) / uDen) := by
      refine sum_le_sum fun w hw => ?_
      rw [hUw w]
      exact mul_le_mul_of_nonneg_right (hleaf w (mem_filter.1 hw).1) (GB_nonneg hνS _ _ _ _)
    have step2 := sum_GB_linear_le hνS (fun _ => N) (Lset.filter lin) (fun w => pv (puW cfg w))
      (fun w => (τW cfg w : ℝ) / ((p : ℝ) - 1)) (fun w => (IW cfg w : ℝ) / uDen)
      (t := (dn : ℝ) / 10 ^ 9) (fun w _ => pv_nonneg _) (fun w _ => by positivity)
      (fun w hw => (hlinR w).1 (mem_filter.1 hw).2) hEB
    refine step1.trans (step2.trans (add_le_add ?_ ?_))
    · -- `Σ pu (u - t) ≤ pv lin1`
      have hσ := fun w => σ_le h (cfg := cfg) w
      have hI : ∑ w ∈ Lset.filter lin, puW cfg w * IW cfg w =
          cfg.pj1 * weightedSum acc.hn + cfg.pj2 * weightedSum acc.hs1 + weightedSum acc.hs2 -
            cfg.pj2 * weightedSum acc.hs2 := by
        have hle : ∀ w ∈ Lset.filter lin, puW cfg w * σ2W cfg w ≤ puW cfg w * σ1W cfg w :=
          fun w _ => Nat.mul_le_mul_left _ (hσ w).1
        have hS21 : weightedSum acc.hs2 ≤ weightedSum acc.hs1 := by
          rw [hS1, hS2]; exact sum_le_sum hle
        have hsub : ∑ w ∈ Lset.filter lin, puW cfg w * (σ1W cfg w - σ2W cfg w) =
            weightedSum acc.hs1 - weightedSum acc.hs2 := by
          rw [hS1, hS2, ← sum_tsub_distrib _ hle]
          exact sum_congr rfl fun w _ => Nat.mul_sub _ _ _
        have e : ∑ w ∈ Lset.filter lin, puW cfg w * IW cfg w =
            cfg.pj1 * weightedSum acc.hn +
              cfg.pj2 * (weightedSum acc.hs1 - weightedSum acc.hs2) + weightedSum acc.hs2 := by
          rw [← hsub, hSN, hS2, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
          refine sum_congr rfl fun w _ => ?_
          unfold IW
          ring
        rw [e, Nat.mul_sub]
        have := Nat.mul_le_mul_left cfg.pj2 hS21
        omega
      have e2 : ∑ w ∈ Lset.filter lin, pv (puW cfg w) * ((IW cfg w : ℝ) / uDen - (dn : ℝ) / 10 ^ 9) =
          pv (∑ w ∈ Lset.filter lin, puW cfg w * IW cfg w) / uDen -
            (dn : ℝ) / 10 ^ 9 * pv (∑ w ∈ Lset.filter lin, puW cfg w) := by
        rw [pv_sum, pv_sum, sum_div, mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun w _ => ?_
        rw [mul_comm (puW cfg w), pv_mul_left]
        field_simp
      rw [e2, hI, ← hSP]
      exact pv_lin1_ge _ _ dn uDen huDen0
    · -- `(EB - 1) Σ pu α ≤ pv lin2`
      have e3 : ∑ w ∈ Lset.filter lin, pv (puW cfg w) * ((τW cfg w : ℝ) / ((p : ℝ) - 1)) =
          pv (weightedSum acc.hn + weightedSum acc.hs1) / ((p : ℝ) - 1) := by
        rw [hSN, hS1, ← sum_add_distrib, pv_sum, sum_div]
        refine sum_congr rfl fun w _ => ?_
        rw [← Nat.mul_add, Nat.sub_add_cancel (σ_le h w).2, mul_comm (puW cfg w), pv_mul_left]
        field_simp
      rw [e3]
      exact pv_lin2_ge EB _ p hp
  -- the FB leaves
  have hL2 : ∑ w ∈ Lset.filter (fun w => ¬ lin w), weight (Ps cfg 0) ν (fun _ => N) w *
        GB S ν (fun _ => N) ((dn : ℝ) / 10 ^ 9)
          (((smooth (Ps cfg 0) w).divisors.card : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth (Ps cfg 0) w)) ≤
      pv (comparisonCost.fbLeaves p dn fb cfg uDen acc.fb 0 0 acc.fb.size) := by
    have step1 : ∑ w ∈ Lset.filter (fun w => ¬ lin w), weight (Ps cfg 0) ν (fun _ => N) w *
          GB S ν (fun _ => N) ((dn : ℝ) / 10 ^ 9)
            (((smooth (Ps cfg 0) w).divisors.card : ℝ) / ((p : ℝ) - 1)) (Up p m (smooth (Ps cfg 0) w)) ≤
        ∑ w ∈ Lset.filter (fun w => ¬ lin w), pv (puW cfg w) * pv (gKey cfg fb dn p uDen (keyW cfg w)) := by
      refine sum_le_sum fun w hw => ?_
      obtain ⟨hwL, hwl⟩ := mem_filter.1 hw
      have hσ := σ_le h (cfg := cfg) w
      have hkey : gKey cfg fb dn p uDen (keyW cfg w) = gUp fb dn p (τW cfg w) (IW cfg w) uDen := by
        obtain ⟨d1, d2, d3⟩ := key_decode (n1 := τW cfg w - σ1W cfg w) (σ1 := σ1W cfg w)
          (σ2 := σ2W cfg w) (M1 := cfg.M1) (M2 := cfg.M2) (sig_lt (le_trans hM.1 hM.2) _)
          (sig_lt hM.1 _)
        unfold gKey keyW
        rw [d1, d2, d3, Nat.sub_add_cancel hσ.2]
        rfl
      have hut : IW cfg w * DDEN ≤ dn * uDen := by
        have h1 : ¬ cfg.It ≤ IW cfg w := hwl
        rw [hIt] at h1
        unfold cdiv at h1
        rw [cdiv_le_iff_le_mul (by unfold DDEN; omega)] at h1
        omega
      have hGw := hG (τW cfg w) (IW cfg w) uDen (one_le_τW h w) huDen0 hut
      rw [hUw w, hkey]
      exact mul_le_mul (hleaf w hwL) hGw (GB_nonneg hνS _ _ _ _) (pv_nonneg _)
    refine step1.trans ?_
    have e4 : ∑ w ∈ Lset.filter (fun w => ¬ lin w), pv (puW cfg w) * pv (gKey cfg fb dn p uDen (keyW cfg w)) =
        ∑ j ∈ range acc.fb.size, pv (getD0 acc.fb j) * pv (gKey cfg fb dn p uDen j) := by
      have hc : ((∑ w ∈ Lset.filter (fun w => ¬ lin w), puW cfg w * gKey cfg fb dn p uDen (keyW cfg w) : ℕ) : ℝ) =
          ((∑ j ∈ range acc.fb.size, getD0 acc.fb j * gKey cfg fb dn p uDen j : ℕ) : ℝ) := by
        rw [hFB]
      push_cast at hc
      have e5 : ∀ a b : ℕ, pv a * pv b = (a : ℝ) * b / (2 ^ 62 * 2 ^ 62) := by
        intro a b; unfold pv; field_simp
      simp only [e5]
      rw [← sum_div, ← sum_div, hc]
    rw [e4, fbLeaves_eq, Nat.zero_add, pv_sum, Nat.zero_add, range_eq_Ico]
    exact sum_le_sum fun j _ => pv_mul_le_mulUp _ _
  linarith

end

end MinModulus.CheckerSound.C
