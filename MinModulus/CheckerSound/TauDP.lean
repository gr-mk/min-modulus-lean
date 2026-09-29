import MinModulus.CheckerSound.Defs
import MinModulus.CheckerSound.TauDPReal

/-!
# `CheckerSound.TauDP` (agent CS-B): soundness of the τ-DP machinery of the checker

STATUS: complete, no `sorry`, no `admit`, no `native_decide`, no new axioms.

Files of CS-B (namespace `MinModulus.CheckerSound.B`):
* `TauDPArray.lean`: exact `ℕ` semantics of the loops (`dpStep_get`, `mkExpLaw_spec`,
  `fbTable_spec`, `sumK_eq_range`, `buildA_top_zero`, `le_acut_of_pow_le`, …);
* `TauDPReal.lean`: real-number specifications of the building blocks (rounding, exact tilts
  `tiltN`, `mkExpLaw` entries vs `ρ`, `facE1`, one DP step up/down, the initial array);
* this file: the statements of `CheckerSound/Interfaces.lean` owned by CS-B, **with the same
  names and statements**, and the `FB`/`G` specifications for CS-C:
  - `BValid_init`, `BValid_addPrime` (B part), `buildA_valid` (A part);
  - `BValid_addToB` (convenience: `addToB` over an index range);
  - `BValid_tilt_mem`, `BValid_meanTau_le`, `BValid_expLostProb_le`, `BValid_lawKept_le`
    (the bounds consumed by `CheckerMath.FB_le_prefix`; `meanTau`/`expLostProb` for every cap);
  - `fbUp_ge` (general) / `BValid_fbUp_ge` (item 4: `FB(pv cP) ≤ pv (fbUp …)`, both branches:
    `FB_le_prefix` for `⌊c⌋ < S0.size`, `FB_le_of_meanTau_le` for the fall-back `EB`);
  - `gUp_ge` (general) / `BValid_gUp_ge` / `BValid_gUp_diag_ge` (item 5: `G(α, u) ≤ pv (gUp …)`
    for `u ≤ t`, via `GB_le_of_bounds`). The linear case `u ≥ t` is
    `CheckerMath.GB_le_of_ge_bounds` / `sum_GB_linear_le` directly (no CS-B code involved).
  - `buildA`-level extras: `AInv` (with the lower array and `EA`), `buildA_inv`, `buildA_eq`,
    `buildA_meanTau_le` (`E[τ_A] ≤ pv EA`, every cap), `buildA_dn_le` (`pv dn[k] ≤ lawKept`).

(The `BValid_*` consequences are plain names, not dot-notation `BValid.*`: dot notation would
need declarations in `MinModulus.CheckerSound.BValid`, outside CS-B's namespace. Note also that
inside `namespace MinModulus.CheckerSound` a local variable named `B` shadows the namespace `B`,
so there use the full names `MinModulus.CheckerSound.B.BValid_addPrime`, etc.)

## Conventions
`pv x = x/2^62`; tilts `tilt (delta0 P)`, equal to the checker's exact `tiltN (deltaN P q)` on
primes `q ≤ X` (`tilt_delta0_eq`); cut-offs `acutA P`, `acutB P` (all `≤ 64`); every DP bound is
for uniform caps `N ≥ 65` (the `Defs` contract). `t = dn/10^9` in `gUp_ge` is `delta0 P p` for
`p ≤ X` (`delta0_of_le`).

## Notes for CS-C / CS-D
* `gUp`'s `num` uses truncated subtraction: `gUp_ge` needs `uNum·10^9 ≤ dn·uDen` (`u ≤ t`), which
  holds at both call sites of `comparisonCost` (FB leaves: `I < It`; `remaining`:
  `k·10^9 < dn(p-1)`).
* `fbUp`'s prefix branch needs `⌊c⌋ ≤ TM = D.size - 1`: `fbUp_ge` takes `K < D.size` (the `okK`
  guard of `comparisonCost`) and `fbTable D K = (S0, PP)`.
-/

namespace MinModulus.CheckerSound.B

open Finset MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Main MinModulus.Smooth

/-! ### The certificate's tilts are the checker's exact tilts -/

theorem two_mul_deltaN_le_DDEN (P : Params) (q : ℕ) : 2 * deltaN P q ≤ DDEN := by
  have := two_mul_deltaN_le P q
  rw [show DDEN = 10 ^ 9 from rfl]
  exact this

theorem deltaN_lt_DDEN (P : Params) (q : ℕ) : deltaN P q < DDEN := by
  have := two_mul_deltaN_le_DDEN P q
  unfold DDEN at *
  omega

/-- On primes `q ≤ X`: `tilt (delta0 P) q = tiltN (deltaN P q)` (both are `10^9/(10^9 - dn)`). -/
theorem tilt_delta0_eq {P : Params} {q : ℕ} (h : q ≤ P.PMAX) :
    tilt (delta0 P) q = tiltN (deltaN P q) := by
  rw [tilt_delta0_of_le h, tiltN_eq (deltaN_lt_DDEN P q)]

theorem tilt_delta0_mem (P : Params) {q : ℕ} (hq : q.Prime) :
    0 ≤ tilt (delta0 P) q ∧ tilt (delta0 P) q ≤ q :=
  tilt_mem (fun q _ => delta0_nonneg P q) (fun q _ => delta0_le_half P q) hq

theorem acutA_le (P : Params) (q : ℕ) : acutA P q ≤ 64 := mkExpLaw_acut_le _ _ _

theorem acutB_le (P : Params) (q : ℕ) : acutB P q ≤ 64 := mkExpLaw_acut_le _ _ _

/-! ### B part: `BState.init`, `BState.addPrime` (Interfaces, CS-B) -/

/-- **(CS-B, Interfaces)** The empty B-part state is valid for `S = ∅` (`τ_∅ = 1`), `N ≥ 2`. -/
theorem BValid_init (P : Params) {N : ℕ} (hN : 2 ≤ N) : BValid P (BState.init N) ∅ where
  mem := fun q hq => absurd hq (notMem_empty q)
  law := fun M _ T hT => by
    have hsz : (BState.init N).D.size = N := size_init N
    rw [hsz] at hT ⊢
    exact (lawKept_empty_eq_init _ _ hN _ T).le
  mean := by
    rw [prod_empty]
    exact pv_ONE.ge
  lost := by
    rw [sum_empty]
    exact pv_nonneg _

/-- **(CS-B, Interfaces)** Adding a prime `q ≤ X` (with its own δ-value `deltaN P q`) to a valid
B-part state for `S ∌ q` gives a valid B-part state for `insert q S`. -/
theorem BValid_addPrime (P : Params) {B : BState} {S : Finset ℕ} (hB : BValid P B S) {q : ℕ}
    (hq : q.Prime) (hqX : q ≤ P.PMAX) (hqS : q ∉ S) :
    BValid P (B.addPrime q (deltaN P q)) (insert q S) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hdn : 2 * deltaN P q ≤ DDEN := two_mul_deltaN_le_DDEN P q
  have hνq : tilt (delta0 P) q = tiltN (deltaN P q) := tilt_delta0_eq hqX
  have hνS : ∀ r ∈ insert q S, 0 ≤ tilt (delta0 P) r ∧ tilt (delta0 P) r ≤ r := by
    intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · exact tilt_delta0_mem P hq
    · exact tilt_delta0_mem P (hB.mem r hr).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · exact ⟨hq, hqX⟩
    · exact hB.mem r hr
  · intro N hN T hT
    have hsz : (B.addPrime q (deltaN P q)).D.size = B.D.size := dpStep_size _ _ _ _ _
    rw [hsz] at hT ⊢
    have hℓ : ∀ a ≤ acutB P q, rho q (tilt (delta0 P) q) N a ≤
        ((mkExpLaw q (deltaN P q) 60).up[a]! : ℝ) / 2 ^ 62 := by
      intro a ha
      rw [hνq]
      have := acutB_le P q
      exact mkExpLaw_rho_le_up hq2 hdn ha (by omega)
    exact lawKept_insert_le_dpStep hqS hνS (fun _ => N) (acutB P) B.D
      (mkExpLaw q (deltaN P q) 60).up (hB.law N hN) hℓ hT
  · show ∏ r ∈ insert q S, (1 + tilt (delta0 P) r / ((r : ℝ) - 1)) ≤
      pv (mulUp B.EB (facE1 q (deltaN P q)))
    rw [prod_insert hqS]
    have h1 : 1 + tilt (delta0 P) q / ((q : ℝ) - 1) ≤ pv (facE1 q (deltaN P q)) := by
      rw [hνq]
      exact facE1_ge hq2 (deltaN_lt_DDEN P q)
    have h0 : 0 ≤ ∏ r ∈ S, (1 + tilt (delta0 P) r / ((r : ℝ) - 1)) := by
      refine prod_nonneg fun r hr => ?_
      have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (hB.mem r hr).1.two_le
      have := (tilt_delta0_mem P (hB.mem r hr).1).1
      have : 0 ≤ tilt (delta0 P) r / ((r : ℝ) - 1) := div_nonneg this (by linarith)
      linarith
    calc (1 + tilt (delta0 P) q / ((q : ℝ) - 1)) * ∏ r ∈ S, (1 + tilt (delta0 P) r / ((r : ℝ) - 1))
        ≤ pv (facE1 q (deltaN P q)) * pv B.EB := mul_le_mul h1 hB.mean h0 (pv_nonneg _)
      _ = pv B.EB * pv (facE1 q (deltaN P q)) := mul_comm _ _
      _ ≤ pv (mulUp B.EB (facE1 q (deltaN P q))) := pv_mul_le_mulUp _ _
  · show ∑ r ∈ insert q S, tilt (delta0 P) r * ((r : ℝ)⁻¹) ^ (acutB P r + 1) ≤
      pv (B.lost + (mkExpLaw q (deltaN P q) 60).lostUp)
    rw [sum_insert hqS, pv_add, add_comm (pv B.lost)]
    refine add_le_add ?_ hB.lost
    rw [hνq]
    exact mkExpLaw_lostUp_ge hq2 hdn

/-- Adding the primes `primes[i], …, primes[i+f-1]` (`addToB`, with `dns[j] = deltaN P primes[j]`)
to a valid B-part state (convenience for CS-D; the image of the index range is added). -/
theorem BValid_addToB (P : Params) (primes dns : Array ℕ) (f : ℕ) :
    ∀ (i : ℕ) (B : BState) (S : Finset ℕ), BValid P B S →
      (∀ j, i ≤ j → j < i + f → dns[j]! = deltaN P primes[j]!) →
      (∀ j, i ≤ j → j < i + f → primes[j]!.Prime ∧ primes[j]! ≤ P.PMAX) →
      (∀ j, i ≤ j → j < i + f → primes[j]! ∉ S) →
      (∀ j j', i ≤ j → j < j' → j' < i + f → primes[j]! ≠ primes[j']!) →
      BValid P (addToB primes dns B i f) (S ∪ (Ico i (i + f)).image (fun j => primes[j]!)) := by
  induction f with
  | zero =>
    intro i B S hB _ _ _ _
    simp only [addToB, Nat.add_zero, Ico_self, image_empty, union_empty]
    exact hB
  | succ f ih =>
    intro i B S hB hdns hpr hnotin hinj
    simp only [addToB]
    rw [hdns i le_rfl (by omega)]
    have hB' := BValid_addPrime P hB (hpr i le_rfl (by omega)).1 (hpr i le_rfl (by omega)).2
      (hnotin i le_rfl (by omega))
    have h := ih (i + 1) _ _ hB' (fun j h1 h2 => hdns j (by omega) (by omega))
      (fun j h1 h2 => hpr j (by omega) (by omega))
      (fun j h1 h2 hmem => by
        rcases mem_insert.1 hmem with h | h
        · exact hinj i j le_rfl (by omega) (by omega) h.symm
        · exact hnotin j (by omega) (by omega) h)
      (fun j j' h1 h2 h3 => hinj j j' (by omega) h2 (by omega))
    have e : insert primes[i]! S ∪ (Ico (i + 1) (i + 1 + f)).image (fun j => primes[j]!) =
        S ∪ (Ico i (i + (f + 1))).image (fun j => primes[j]!) := by
      rw [show i + 1 + f = i + (f + 1) by omega, ← insert_Ico_add_one_left_eq_Ico (by omega : i < i + (f + 1)),
        image_insert, insert_union, union_insert]
    rw [e] at h
    exact h

/-! ### Consequences of `BValid` (the hypotheses of `FB_le_prefix`, for CS-C) -/

section BValidConsequences

variable {P : Params} {B : BState} {S : Finset ℕ}

theorem BValid_tilt_mem (hB : BValid P B S) :
    ∀ q ∈ S, 0 ≤ tilt (delta0 P) q ∧ tilt (delta0 P) q ≤ q :=
  fun q hq => tilt_delta0_mem P (hB.mem q hq).1

/-- `E[τ_S] ≤ pv EB`, every cap. -/
theorem BValid_meanTau_le (hB : BValid P B S) (γ : ℕ → ℕ) :
    meanTau S (tilt (delta0 P)) γ ≤ pv B.EB :=
  (CheckerMath.meanTau_le (fun q hq => (hB.mem q hq).1.one_lt)
    (fun q hq => ((BValid_tilt_mem hB) q hq).1) γ).trans hB.mean

/-- `P(some v_q > acutB q) ≤ pv lost`, every cap. -/
theorem BValid_expLostProb_le (hB : BValid P B S) (γ : ℕ → ℕ) :
    expLostProb S (tilt (delta0 P)) γ (acutB P) ≤ pv B.lost :=
  (CheckerMath.expLostProb_le (BValid_tilt_mem hB) γ (acutB P)).trans hB.lost

/-- `P(τ_S = T, kept) ≤ pv D[T]` for `T < D.size`, uniform caps `N ≥ 65`. -/
theorem BValid_lawKept_le (hB : BValid P B S) {N : ℕ} (hN : 65 ≤ N) {T : ℕ} (hT : T < B.D.size) :
    lawKept S (tilt (delta0 P)) (fun _ => N) (B.D.size - 1) (acutB P) T ≤ pv B.D[T]! :=
  hB.law N hN T hT

end BValidConsequences

/-! ### `fbTable` + `fbUp` (item 4) -/

/-- `Σ_{i < k} S0[i] ≤ 2^20 · PP[k]` (each `⌈S0[i]/2^20⌉` rounds up). -/
theorem sum_S0val_le_PPval (D : Array ℕ) (k : ℕ) :
    ∑ i ∈ range k, S0val D i ≤ PPval D k * 2 ^ 20 := by
  unfold PPval
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [Nat.shiftRight_eq_div_pow]
  have := cdiv_spec (a := S0val D i) (b := 2 ^ 20) (by positivity)
  unfold cdiv at this
  rw [show S0val D i + 2 ^ 20 - 1 = S0val D i + 1048575 by omega] at this
  exact this

theorem preS0_pv_eq (D : Array ℕ) (i : ℕ) :
    preS0 (fun T => pv D[T]!) i = pv (S0val D i) := by
  unfold preS0 S0val pv
  push_cast
  rw [sum_div]

/-- **`fbUp` bounds `FB`** (item 4), general form: if `D ≥ P(τ = ·, kept)` on `[0, D.size)`,
`EB ≥ E[τ]`, `lost ≥ P(some exponent > acut)`, `K < D.size`, and `(S0, PP) = fbTable D K`,
then `FB(pv cP) ≤ pv (fbUp EB lost S0 PP cP)` for every `cP` (both branches). -/
theorem fbUp_ge {S : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ)
    (acut : ℕ → ℕ) (D : Array ℕ) {K : ℕ} (hK : K < D.size)
    (hD : ∀ T < D.size, lawKept S ν γ (D.size - 1) acut T ≤ pv D[T]!)
    (EB lost : ℕ) (hEB : meanTau S ν γ ≤ pv EB) (hP : expLostProb S ν γ acut ≤ pv lost)
    {S0 PP : Array ℕ} (hSP : fbTable D K = (S0, PP)) (cP : ℕ) :
    FB S ν γ (pv cP) ≤ pv (fbUp EB lost S0 PP cP) := by
  have hspec := fbTable_spec D K
  rw [hSP] at hspec
  dsimp only at hspec
  obtain ⟨hS0size, -, hent⟩ := hspec
  have hc0 : 0 ≤ pv cP := pv_nonneg cP
  unfold fbUp
  dsimp only
  split_ifs with hk
  · rw [hS0size] at hk
    have hkK : cP / ONE ≤ K := by omega
    obtain ⟨hS0k, hPPk⟩ := hent (cP / ONE) hkK
    rw [hS0k, hPPk]
    have hONE : (0 : ℕ) < ONE := zero_lt_ONE
    have hmod : ((cP % ONE : ℕ) : ℝ) + 2 ^ 62 * ((cP / ONE : ℕ) : ℝ) = (cP : ℝ) := by
      rw [← cast_ONE]
      exact_mod_cast Nat.mod_add_div cP ONE
    have hk1 : ((cP / ONE : ℕ) : ℝ) ≤ pv cP := by
      unfold pv
      rw [le_div_iff₀ two_pow_62_pos]
      have : (0 : ℝ) ≤ ((cP % ONE : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hk2 : pv cP < ((cP / ONE : ℕ) : ℝ) + 1 := by
      unfold pv
      rw [div_lt_iff₀ two_pow_62_pos]
      have h1 : cP % ONE < ONE := Nat.mod_lt _ hONE
      have h2 : ((cP % ONE : ℕ) : ℝ) < 2 ^ 62 := by rw [← cast_ONE]; exact_mod_cast h1
      linarith
    have h := FB_le_prefix hν γ hc0 (D.size - 1) acut (pv EB) hEB (fun T => pv D[T]!)
      (fun T hT => hD T (by omega)) (pv lost) hP hk1 hk2 (by omega)
    refine h.trans ?_
    simp only [preS0_pv_eq]
    -- the three rounded pieces
    have e1 : ∑ i ∈ range (cP / ONE), pv (S0val D i) ≤ pv (PPval D (cP / ONE) <<< 20) := by
      rw [Nat.shiftLeft_eq]
      have := sum_S0val_le_PPval D (cP / ONE)
      unfold pv
      rw [← sum_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast this) two_pow_62_pos.le
    have e2 : (pv cP - ((cP / ONE : ℕ) : ℝ)) * pv (S0val D (cP / ONE)) ≤
        pv (mulUp (cP % ONE) (S0val D (cP / ONE))) := by
      have : pv cP - ((cP / ONE : ℕ) : ℝ) = pv (cP % ONE) := by
        unfold pv
        field_simp
        linarith
      rw [this]
      exact pv_mul_le_mulUp _ _
    have e3 : pv cP * pv lost ≤ pv (mulUp cP lost) := pv_mul_le_mulUp _ _
    have e4 : pv EB + pv (PPval D (cP / ONE) <<< 20) + pv (mulUp (cP % ONE) (S0val D (cP / ONE)))
        + pv (mulUp cP lost) - pv cP ≤
        pv (EB + PPval D (cP / ONE) <<< 20 + mulUp (cP % ONE) (S0val D (cP / ONE)) +
          mulUp cP lost - cP) := by
      simp only [← pv_add]
      unfold pv
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (sub_le_cast_tsub _ _) two_pow_62_pos.le
    linarith
  · exact FB_le_of_meanTau_le hν γ hc0 hEB

/-- **`fbUp` bounds `FB`** for a valid B-part state (item 4; uniform caps `N ≥ 65`). -/
theorem BValid_fbUp_ge {P : Params} {B : BState} {S : Finset ℕ} (hB : BValid P B S) {K : ℕ}
    (hK : K < B.D.size) {S0 PP : Array ℕ} (hSP : fbTable B.D K = (S0, PP)) {N : ℕ}
    (hN : 65 ≤ N) (cP : ℕ) :
    FB S (tilt (delta0 P)) (fun _ => N) (pv cP) ≤ pv (fbUp B.EB B.lost S0 PP cP) :=
  fbUp_ge (BValid_tilt_mem hB) (fun _ => N) (acutB P) B.D hK (fun T hT => hB.law N hN T hT) B.EB B.lost
    ((BValid_meanTau_le hB) _) ((BValid_expLostProb_le hB) _) hSP cP

/-! ### `gUp` (item 5) -/

/-- **`gUp` bounds `G` in the FB case** (item 5), general form: for `u ≤ t` (`uNum·10^9 ≤ dn·uDen`,
`t = dn/10^9`, `u' = uNum/uDen`), `τ ≥ 1`, `p ≥ 2`, and any upper bound `fb` of `FB` on P-values,
`G(α, u) ≤ pv (gUp fb dn p τ uNum uDen)` for all `α ≤ τ/(p-1)`, `u ≤ u'`
(`CheckerMath.GB_le_of_bounds` with `α' = τ/(p-1)`, `c = pv cP ≤ 1 + (t - u')/α'`). -/
theorem gUp_ge {S : Finset ℕ} {ν : ℕ → ℝ} (hν : ∀ q ∈ S, 0 ≤ ν q ∧ ν q ≤ q) (γ : ℕ → ℕ)
    (fb : ℕ → ℕ) (hfb : ∀ cP : ℕ, FB S ν γ (pv cP) ≤ pv (fb cP)) {dn p τ uNum uDen : ℕ}
    (hp : 2 ≤ p) (hτ : 1 ≤ τ) (huDen : 0 < uDen) (hut : uNum * DDEN ≤ dn * uDen) {α u : ℝ}
    (hα : α ≤ (τ : ℝ) / ((p : ℝ) - 1)) (hu : u ≤ (uNum : ℝ) / uDen) :
    GB S ν γ ((dn : ℝ) / 10 ^ 9) α u ≤ pv (gUp fb dn p τ uNum uDen) := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  have huD : (0 : ℝ) < uDen := by exact_mod_cast huDen
  have hα' : (0 : ℝ) < (τ : ℝ) / ((p : ℝ) - 1) := div_pos hτ0 hp1
  set cP := ONE + (dn * uDen - uNum * DDEN) * (p - 1) * ONE / (DDEN * uDen * τ) with hcP
  -- `pv cP ≤ 1 + (t - u')/α'`
  have hc : pv cP ≤ 1 + ((dn : ℝ) / 10 ^ 9 - (uNum : ℝ) / uDen) / ((τ : ℝ) / ((p : ℝ) - 1)) := by
    have hden : 0 < DDEN * uDen * τ := Nat.mul_pos (Nat.mul_pos (by unfold DDEN; omega) huDen) hτ
    have hfl := Nat.div_mul_le_self ((dn * uDen - uNum * DDEN) * (p - 1) * ONE) (DDEN * uDen * τ)
    set M := (dn * uDen - uNum * DDEN) * (p - 1) * ONE / (DDEN * uDen * τ) with hM
    have hfl' : (M : ℝ) * ((DDEN : ℕ) * uDen * τ : ℝ) ≤
        (((dn * uDen - uNum * DDEN : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ) * 2 ^ 62) := by
      rw [← cast_ONE]
      exact_mod_cast hfl
    push_cast [Nat.cast_sub hut, Nat.cast_sub (by omega : 1 ≤ p)] at hfl'
    rw [cast_DDEN] at hfl'
    have hpv : pv cP = 1 + (M : ℝ) / 2 ^ 62 := by
      unfold pv
      rw [hcP]
      push_cast
      rw [cast_ONE]
      field_simp
    rw [hpv]
    have hden' : (0 : ℝ) < 10 ^ 9 * uDen * τ := by positivity
    have hMle : (M : ℝ) / 2 ^ 62 ≤
        ((dn : ℝ) * uDen - uNum * 10 ^ 9) * ((p : ℝ) - 1) / (10 ^ 9 * uDen * τ) := by
      rw [div_le_div_iff₀ two_pow_62_pos hden']
      linarith
    have e : ((dn : ℝ) / 10 ^ 9 - (uNum : ℝ) / uDen) / ((τ : ℝ) / ((p : ℝ) - 1)) =
        ((dn : ℝ) * uDen - uNum * 10 ^ 9) * ((p : ℝ) - 1) / (10 ^ 9 * uDen * τ) := by
      field_simp
    rw [e]
    linarith
  have h := GB_le_of_bounds hν γ ((dn : ℝ) / 10 ^ 9) hα hα' hu hc (hfb cP)
  refine h.trans ?_
  unfold gUp
  dsimp only
  rw [← hcP]
  unfold pv
  have hq : ((τ : ℝ) / ((p : ℝ) - 1)) * ((fb cP : ℝ) / 2 ^ 62) =
      ((τ * fb cP : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) / 2 ^ 62 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    field_simp
  rw [hq]
  exact div_le_div_of_nonneg_right (cdiv_ge_real (by omega)) two_pow_62_pos.le

/-- **`gUp` with `fb = fbUp` of a valid B-part state** (item 5, the form used in
`comparisonCost`: `fb = fun cP => fbUp B.EB B.lost S0 PP cP`, `(S0, PP) = fbTable B.D K`). -/
theorem BValid_gUp_ge {P : Params} {B : BState} {S : Finset ℕ} (hB : BValid P B S) {K : ℕ}
    (hK : K < B.D.size) {S0 PP : Array ℕ} (hSP : fbTable B.D K = (S0, PP)) {N : ℕ}
    (hN : 65 ≤ N) {dn p τ uNum uDen : ℕ} (hp : 2 ≤ p) (hτ : 1 ≤ τ) (huDen : 0 < uDen)
    (hut : uNum * DDEN ≤ dn * uDen) {α u : ℝ} (hα : α ≤ (τ : ℝ) / ((p : ℝ) - 1))
    (hu : u ≤ (uNum : ℝ) / uDen) :
    GB S (tilt (delta0 P)) (fun _ => N) ((dn : ℝ) / 10 ^ 9) α u ≤
      pv (gUp (fun cP => fbUp B.EB B.lost S0 PP cP) dn p τ uNum uDen) :=
  gUp_ge (BValid_tilt_mem hB) (fun _ => N) _ (fun cP => (BValid_fbUp_ge hB) hK hSP hN cP) hp hτ huDen hut hα hu

/-- **`gUp` on the diagonal** `α = u = k/(p-1)` (the `remaining` loop of `comparisonCost`, which
calls `gUp fb dn p k k (p - 1)` when `k·10^9 < dn·(p-1)`). -/
theorem BValid_gUp_diag_ge {P : Params} {B : BState} {S : Finset ℕ} (hB : BValid P B S) {K : ℕ}
    (hK : K < B.D.size) {S0 PP : Array ℕ} (hSP : fbTable B.D K = (S0, PP)) {N : ℕ}
    (hN : 65 ≤ N) {dn p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k) (hkt : k * DDEN ≤ dn * (p - 1)) :
    GB S (tilt (delta0 P)) (fun _ => N) ((dn : ℝ) / 10 ^ 9) ((k : ℝ) / ((p : ℝ) - 1))
        ((k : ℝ) / ((p : ℝ) - 1)) ≤
      pv (gUp (fun cP => fbUp B.EB B.lost S0 PP cP) dn p k k (p - 1)) := by
  refine BValid_gUp_ge hB hK hSP hN hp hk (by omega) hkt le_rfl (le_of_eq ?_)
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]

/-! ### A part: `buildA` (Interfaces, CS-B) -/

/-- Invariant of the A-part DP loop `buildA.go` (upper and lower arrays, `EA`), uniform caps
`N ≥ 65`, `TM = KMAX` (written `KMAX + 1 - 1`, the array size minus one). -/
structure AInv (P : Params) (up dn : Array ℕ) (EA : ℕ) (S : Finset ℕ) : Prop where
  mem : ∀ q ∈ S, q.Prime ∧ q ≤ P.PMAX
  up_size : up.size = P.KMAX + 1
  dn_size : dn.size = P.KMAX + 1
  up_ge : ∀ N, 65 ≤ N → ∀ k, k < P.KMAX + 1 →
    lawKept S (tilt (delta0 P)) (fun _ => N) (P.KMAX + 1 - 1) (acutA P) k ≤ pv up[k]!
  dn_le : ∀ N, 65 ≤ N → ∀ k, k < P.KMAX + 1 →
    pv dn[k]! ≤ lawKept S (tilt (delta0 P)) (fun _ => N) (P.KMAX + 1 - 1) (acutA P) k
  mean : ∏ q ∈ S, (1 + tilt (delta0 P) q / ((q : ℝ) - 1)) ≤ pv EA

theorem AInv.init (P : Params) (hK : 1 ≤ P.KMAX) :
    AInv P ((Array.replicate (P.KMAX + 1) 0).set! 1 ONE)
      ((Array.replicate (P.KMAX + 1) 0).set! 1 ONE) ONE ∅ where
  mem := fun q hq => absurd hq (notMem_empty q)
  up_size := size_init _
  dn_size := size_init _
  up_ge := fun N _ k _ => (lawKept_empty_eq_init _ _ (by omega) _ k).le
  dn_le := fun N _ k _ => (lawKept_empty_eq_init _ _ (by omega) _ k).ge
  mean := by
    rw [prod_empty]
    exact pv_ONE.ge

/-- One step of `buildA.go`: adding the prime `q ≤ X`. -/
theorem AInv.step {P : Params} {up dn : Array ℕ} {EA : ℕ} {S : Finset ℕ} (h : AInv P up dn EA S)
    {q : ℕ} (hq : q.Prime) (hqX : q ≤ P.PMAX) (hqS : q ∉ S) :
    AInv P (dpStep true up (P.KMAX + 1) (mkExpLaw q (deltaN P q) 62).up
        (mkExpLaw q (deltaN P q) 62).acut)
      (dpStep false dn (P.KMAX + 1) (mkExpLaw q (deltaN P q) 62).dn
        (mkExpLaw q (deltaN P q) 62).acut)
      (mulUp EA (facE1 q (deltaN P q))) (insert q S) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hdn : 2 * deltaN P q ≤ DDEN := two_mul_deltaN_le_DDEN P q
  have hνq : tilt (delta0 P) q = tiltN (deltaN P q) := tilt_delta0_eq hqX
  have hνS : ∀ r ∈ insert q S, 0 ≤ tilt (delta0 P) r ∧ tilt (delta0 P) r ≤ r := by
    intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · exact tilt_delta0_mem P hq
    · exact tilt_delta0_mem P (h.mem r hr).1
  refine ⟨?_, dpStep_size _ _ _ _ _, dpStep_size _ _ _ _ _, ?_, ?_, ?_⟩
  · intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · exact ⟨hq, hqX⟩
    · exact h.mem r hr
  · intro N hN k hk
    have hℓ : ∀ a ≤ acutA P q, rho q (tilt (delta0 P) q) N a ≤
        ((mkExpLaw q (deltaN P q) 62).up[a]! : ℝ) / 2 ^ 62 := by
      intro a ha
      rw [hνq]
      have := acutA_le P q
      exact mkExpLaw_rho_le_up hq2 hdn ha (by omega)
    exact lawKept_insert_le_dpStep hqS hνS (fun _ => N) (acutA P) up
      (mkExpLaw q (deltaN P q) 62).up (h.up_ge N hN) hℓ hk
  · intro N hN k hk
    have hℓ : ∀ a ≤ acutA P q, ((mkExpLaw q (deltaN P q) 62).dn[a]! : ℝ) / 2 ^ 62 ≤
        rho q (tilt (delta0 P) q) N a := by
      intro a ha
      rw [hνq]
      have := acutA_le P q
      exact mkExpLaw_dn_le_rho hq2 hdn ha (by omega)
    exact dpStep_le_lawKept_insert hqS (fun _ => N) (acutA P) dn
      (mkExpLaw q (deltaN P q) 62).dn (h.dn_le N hN) hℓ hk
  · rw [prod_insert hqS]
    have h1 : 1 + tilt (delta0 P) q / ((q : ℝ) - 1) ≤ pv (facE1 q (deltaN P q)) := by
      rw [hνq]
      exact facE1_ge hq2 (deltaN_lt_DDEN P q)
    have h0 : 0 ≤ ∏ r ∈ S, (1 + tilt (delta0 P) r / ((r : ℝ) - 1)) := by
      refine prod_nonneg fun r hr => ?_
      have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (h.mem r hr).1.two_le
      have := (tilt_delta0_mem P (h.mem r hr).1).1
      have : 0 ≤ tilt (delta0 P) r / ((r : ℝ) - 1) := div_nonneg this (by linarith)
      linarith
    calc (1 + tilt (delta0 P) q / ((q : ℝ) - 1)) * ∏ r ∈ S, (1 + tilt (delta0 P) r / ((r : ℝ) - 1))
        ≤ pv (facE1 q (deltaN P q)) * pv EA := mul_le_mul h1 h.mean h0 (pv_nonneg _)
      _ = pv EA * pv (facE1 q (deltaN P q)) := mul_comm _ _
      _ ≤ pv (mulUp EA (facE1 q (deltaN P q))) := pv_mul_le_mulUp _ _

/-- The loop `buildA.go` over the indices `[i, i + f)`. -/
theorem buildA_go_inv (P : Params) (aps adns : Array ℕ)
    (hadns : ∀ j < aps.size, adns[j]! = deltaN P aps[j]!) (f : ℕ) :
    ∀ (i : ℕ) (up dn : Array ℕ) (EA : ℕ) (S : Finset ℕ), i + f ≤ aps.size → AInv P up dn EA S →
      (∀ j, i ≤ j → j < i + f → aps[j]!.Prime ∧ aps[j]! ≤ P.PMAX) →
      (∀ j, i ≤ j → j < i + f → aps[j]! ∉ S) →
      (∀ j j', i ≤ j → j < j' → j' < i + f → aps[j]! ≠ aps[j']!) →
      AInv P (buildA.go aps adns P.KMAX i up dn EA f).1 (buildA.go aps adns P.KMAX i up dn EA f).2.1
        (buildA.go aps adns P.KMAX i up dn EA f).2.2
        (S ∪ (Ico i (i + f)).image (fun j => aps[j]!)) := by
  induction f with
  | zero =>
    intro i up dn EA S _ h _ _ _
    simp only [buildA.go, Nat.add_zero, Ico_self, image_empty, union_empty]
    exact h
  | succ f ih =>
    intro i up dn EA S hsz h hpr hnotin hinj
    rw [buildA.go.eq_2, hadns i (by omega)]
    have h' := h.step (hpr i le_rfl (by omega)).1 (hpr i le_rfl (by omega)).2
      (hnotin i le_rfl (by omega))
    have hres := ih (i + 1) _ _ _ _ (by omega) h' (fun j h1 h2 => hpr j (by omega) (by omega))
      (fun j h1 h2 hmem => by
        rcases mem_insert.1 hmem with h | h
        · exact hinj i j le_rfl (by omega) (by omega) h.symm
        · exact hnotin j (by omega) (by omega) h)
      (fun j j' h1 h2 h3 => hinj j j' (by omega) h2 (by omega))
    have e : insert aps[i]! S ∪ (Ico (i + 1) (i + 1 + f)).image (fun j => aps[j]!) =
        S ∪ (Ico i (i + (f + 1))).image (fun j => aps[j]!) := by
      rw [show i + 1 + f = i + (f + 1) by omega,
        ← insert_Ico_add_one_left_eq_Ico (by omega : i < i + (f + 1)), image_insert, insert_union,
        union_insert]
    rw [e] at hres
    exact hres

/-- Index facts for a duplicate-free array. -/
theorem image_getElem!_eq_toFinset (aps : Array ℕ) :
    (Ico 0 aps.size).image (fun j => aps[j]!) = aps.toList.toFinset := by
  ext q
  simp only [mem_image, mem_Ico, List.mem_toFinset, Array.mem_toList_iff, Array.mem_iff_getElem]
  constructor
  · rintro ⟨j, ⟨-, hj⟩, rfl⟩
    exact ⟨j, hj, (getElem!_pos aps j hj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, ⟨Nat.zero_le j, hj⟩, getElem!_pos aps j hj⟩

theorem getElem!_injOn_of_nodup {aps : Array ℕ} (hnd : aps.toList.Nodup) {j j' : ℕ}
    (hjj' : j < j') (hj' : j' < aps.size) : aps[j]! ≠ aps[j']! := by
  have hj : j < aps.size := by omega
  rw [getElem!_pos aps j hj, getElem!_pos aps j' hj']
  intro heq
  have h1 : aps.toList[j]'(by rw [Array.length_toList]; exact hj) =
      aps.toList[j']'(by rw [Array.length_toList]; exact hj') := by
    rw [Array.getElem_toList, Array.getElem_toList]
    exact heq
  have := (hnd.getElem_inj_iff).1 h1
  omega

/-- The full state computed by `buildA`: arrays and `EA` from the loop, then `tailA` and `kTop`. -/
theorem buildA_eq (aps adns : Array ℕ) (KMAX : ℕ) :
    buildA aps adns KMAX =
      { up := (buildA.go aps adns KMAX 0 ((Array.replicate (KMAX + 1) 0).set! 1 ONE)
            ((Array.replicate (KMAX + 1) 0).set! 1 ONE) ONE aps.size).1
        dn := (buildA.go aps adns KMAX 0 ((Array.replicate (KMAX + 1) 0).set! 1 ONE)
            ((Array.replicate (KMAX + 1) 0).set! 1 ONE) ONE aps.size).2.1
        EA := (buildA.go aps adns KMAX 0 ((Array.replicate (KMAX + 1) 0).set! 1 ONE)
            ((Array.replicate (KMAX + 1) 0).set! 1 ONE) ONE aps.size).2.2
        tailA := (buildA.go aps adns KMAX 0 ((Array.replicate (KMAX + 1) 0).set! 1 ONE)
            ((Array.replicate (KMAX + 1) 0).set! 1 ONE) ONE aps.size).2.2 -
          buildA.sumK (buildA.go aps adns KMAX 0 ((Array.replicate (KMAX + 1) 0).set! 1 ONE)
            ((Array.replicate (KMAX + 1) 0).set! 1 ONE) ONE aps.size).2.1 1 0 KMAX
        kTop := buildA.top (buildA.go aps adns KMAX 0 ((Array.replicate (KMAX + 1) 0).set! 1 ONE)
            ((Array.replicate (KMAX + 1) 0).set! 1 ONE) ONE aps.size).1 KMAX KMAX } := by
  unfold buildA
  rfl

/-- The loop invariant for the whole `buildA` (with the lower array and `EA`). -/
theorem buildA_inv (P : Params) (hK : 1 ≤ P.KMAX) (aps adns : Array ℕ)
    (hnd : aps.toList.Nodup) (hpr : ∀ q ∈ aps.toList, q.Prime ∧ q ≤ P.PMAX)
    (hadns : adns = aps.map (deltaN P)) :
    AInv P (buildA aps adns P.KMAX).up (buildA aps adns P.KMAX).dn (buildA aps adns P.KMAX).EA
      aps.toList.toFinset := by
  have hadns' : ∀ j < aps.size, adns[j]! = deltaN P aps[j]! := by
    intro j hj
    subst hadns
    rw [getElem!_pos (aps.map (deltaN P)) j (by rw [Array.size_map]; exact hj),
      Array.getElem_map, getElem!_pos aps j hj]
  have hmem : ∀ j < aps.size, aps[j]! ∈ aps.toList := by
    intro j hj
    rw [getElem!_pos aps j hj, Array.mem_toList_iff]
    exact Array.getElem_mem hj
  have h := buildA_go_inv P aps adns hadns' aps.size 0 _ _ _ ∅ (by omega) (AInv.init P hK)
    (fun j _ hj => hpr _ (hmem j (by omega))) (fun j _ _ => notMem_empty _)
    (fun j j' _ hjj' hj' => getElem!_injOn_of_nodup hnd hjj' (by omega))
  rw [empty_union, Nat.zero_add, image_getElem!_eq_toFinset] at h
  rw [buildA_eq]
  exact h

/-- **(CS-B, Interfaces)** `buildA` of a duplicate-free array of primes `≤ X` (any order), with
their own δ-values, is a valid A-part state for the set of these primes. -/
theorem buildA_valid (P : Params) (hK : 1 ≤ P.KMAX) (aps adns : Array ℕ)
    (hnd : aps.toList.Nodup) (hpr : ∀ q ∈ aps.toList, q.Prime ∧ q ≤ P.PMAX)
    (hadns : adns = aps.map (deltaN P)) :
    AValid P (buildA aps adns P.KMAX) aps.toList.toFinset := by
  have hinv := buildA_inv P hK aps adns hnd hpr hadns
  have hK1 : P.KMAX + 1 - 1 = P.KMAX := Nat.add_sub_cancel _ _
  set S := aps.toList.toFinset with hS
  have hνS : ∀ q ∈ S, 0 ≤ tilt (delta0 P) q ∧ tilt (delta0 P) q ≤ q :=
    fun q hq => tilt_delta0_mem P (hinv.mem q hq).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N hN k hk
    have := hinv.up_ge N hN k (by omega)
    rwa [hK1] at this
  · intro N hN
    -- `tailA = EA - Σ_k k·dn[k]` (`lostMass_le_of_lower`)
    have hEA : meanTau S (tilt (delta0 P)) (fun _ => N) ≤ pv (buildA aps adns P.KMAX).EA :=
      (CheckerMath.meanTau_le (fun q hq => (hinv.mem q hq).1.one_lt) (fun q hq => (hνS q hq).1)
        _).trans hinv.mean
    have hdn : ∀ T ≤ P.KMAX, pv (buildA aps adns P.KMAX).dn[T]! ≤
        lawKept S (tilt (delta0 P)) (fun _ => N) P.KMAX (acutA P) T := by
      intro T hT
      have := hinv.dn_le N hN T (by omega)
      rwa [hK1] at this
    have h := lostMass_le_of_lower (fun _ => N) P.KMAX (acutA P) _ hEA
      (fun T => pv (buildA aps adns P.KMAX).dn[T]!) hdn
    refine h.trans ?_
    have hsum : ∑ T ∈ range (P.KMAX + 1), (T : ℝ) * pv (buildA aps adns P.KMAX).dn[T]! =
        pv (buildA.sumK (buildA aps adns P.KMAX).dn 1 0 P.KMAX) := by
      rw [sumK_eq_range]
      unfold pv
      push_cast
      rw [sum_div]
      exact sum_congr rfl fun T _ => by ring
    rw [hsum]
    have htail : (buildA aps adns P.KMAX).tailA =
        (buildA aps adns P.KMAX).EA - buildA.sumK (buildA aps adns P.KMAX).dn 1 0 P.KMAX := by
      rw [buildA_eq]
    rw [htail]
    unfold pv
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (sub_le_cast_tsub _ _) two_pow_62_pos.le
  · intro k hk
    by_cases hkK : k ≤ P.KMAX
    · have htop : (buildA aps adns P.KMAX).kTop =
          buildA.top (buildA aps adns P.KMAX).up P.KMAX P.KMAX := by
        rw [buildA_eq]
      rw [htop] at hk
      exact buildA_top_zero _ P.KMAX hk hkK
    · exact getElem!_of_size_le _ (by rw [hinv.up_size]; omega)
  · intro q hq
    exact two_pow_lt_pow_acut_succ (hinv.mem q hq).1.two_le _ (by norm_num)

/-- `buildA`'s `EA` bounds `E[τ_A]` (every cap). -/
theorem buildA_meanTau_le (P : Params) (hK : 1 ≤ P.KMAX) (aps adns : Array ℕ)
    (hnd : aps.toList.Nodup) (hpr : ∀ q ∈ aps.toList, q.Prime ∧ q ≤ P.PMAX)
    (hadns : adns = aps.map (deltaN P)) (γ : ℕ → ℕ) :
    meanTau aps.toList.toFinset (tilt (delta0 P)) γ ≤ pv (buildA aps adns P.KMAX).EA := by
  have hinv := buildA_inv P hK aps adns hnd hpr hadns
  exact (CheckerMath.meanTau_le (fun q hq => (hinv.mem q hq).1.one_lt)
    (fun q hq => (tilt_delta0_mem P (hinv.mem q hq).1).1) γ).trans hinv.mean

/-- `buildA`'s lower array: `pv dn[k] ≤ P(τ_A = k, kept)` for `k ≤ KMAX`, caps `N ≥ 65`. -/
theorem buildA_dn_le (P : Params) (hK : 1 ≤ P.KMAX) (aps adns : Array ℕ)
    (hnd : aps.toList.Nodup) (hpr : ∀ q ∈ aps.toList, q.Prime ∧ q ≤ P.PMAX)
    (hadns : adns = aps.map (deltaN P)) {N : ℕ} (hN : 65 ≤ N) {k : ℕ} (hk : k ≤ P.KMAX) :
    pv (buildA aps adns P.KMAX).dn[k]! ≤
      lawKept aps.toList.toFinset (tilt (delta0 P)) (fun _ => N) P.KMAX (acutA P) k := by
  have hinv := buildA_inv P hK aps adns hnd hpr hadns
  have := hinv.dn_le N hN k (by omega)
  rwa [Nat.add_sub_cancel] at this

end MinModulus.CheckerSound.B
