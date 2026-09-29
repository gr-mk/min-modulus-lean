import MinModulus.Checker2Sound.SBHCode
import MinModulus.Checker2Math.SBHLawDFS

/-!
# `Checker2Sound.SBHDfs` (agent L2-D): the DFS of `sbhCost` against L2-A's DFS model

STATUS: complete (fully proved; agent L2-D). Axioms: `propext`, `Classical.choice`, `Quot.sound`.

`dfs_nodeVal`: for any `DfsCfg` whose arrays satisfy the one-prime bounds (`pm` ≥ point masses,
`h` ≥ `h_N(a)`, `REW[j+1]` ≥ `C·∏_{i > j} E[v_i + 1]`), any leaf function `G ≥ 0` with
`G ≤ C·τ_S` and whose leaves are bounded by `leafAdd`, a run of `dfsNode … 0 ONE2 1 0` that ends
with `ok = true` accumulates at least `E_S[G]` (in W-values). This is the abstract `dfs_sound`
(`SBHCode`) instantiated with `V = A.nodeVal` (L2-A's `SBHLawDFS`: `nodeVal_eq_expVal`,
`nodeVal_of_le`, `expVal_le`).
-/

namespace MinModulus.Checker2Sound.D

open MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.Checker2Math MinModulus.Smooth
  MinModulus.CheckerMath Finset

theorem tauN_update_of_mem {S : Finset ℕ} {q : ℕ} (hq : q ∈ S) {u : ℕ → ℕ} (hu : u q = 0)
    (a : ℕ) : tauN S (Function.update u q a) = tauN S u * (a + 1) := by
  have hS : S = insert q (S.erase q) := (insert_erase hq).symm
  have hq' : q ∉ S.erase q := notMem_erase q S
  rw [hS, tauN_insert_update hq', tauN_insert hq', hu, zero_add, one_mul]

/-- **The DFS of `sbhCost` accumulates at least `E_S[G]`.** -/
theorem dfs_nodeVal (c : DfsCfg) (Q : ℕ → ℕ) (n N : ℕ) (ν : ℕ → ℝ) (G : (ℕ → ℕ) → ℝ)
    (kkf sp : ℕ → ℕ) (C : ℝ) (hn : c.nS = n)
    (hinj : Set.InjOn Q (Set.Iio n)) (hq1 : ∀ i < n, 1 < Q i)
    (hν : ∀ i < n, 0 ≤ ν (Q i) ∧ ν (Q i) ≤ Q i)
    (hG0 : ∀ w, 0 ≤ G w) (hC : 0 ≤ C) (hG : ∀ w, G w ≤ C * (tauN (A.sufSet Q n 0) w : ℝ))
    (hacut : ∀ j < n, c.acut[j]! < N)
    (hkk : ∀ j < n, c.kk[j]! = kkf j) (hstride : ∀ j < n, c.stride[j]! = sp j)
    (hρ : ∀ j < n, ∀ a ≤ c.acut[j]!, rho (Q j) (ν (Q j)) N a ≤ pv (c.pm[j]!)[a]!)
    (hh : ∀ j < n, ∀ a ≤ c.acut[j]! + 1, hMass (Q j) (ν (Q j)) N a ≤ pv (c.h[j]!)[a]!)
    (hREW : ∀ j < n, C * ∏ q ∈ A.sufSet Q n (j + 1), (1 + ν q / ((q : ℝ) - 1)) ≤ wv c.REW[j + 1]!)
    (hleaf : ∀ (u : ℕ → ℕ) (pat P : ℕ) (acc : DfsAcc), (∀ i < n, u (Q i) ≤ c.acut[i]!) →
      pat = ∑ i ∈ range n, min (u (Q i)) (kkf i) * sp i →
      (leafAdd c P (tauN (A.sufSet Q n 0) u) pat acc).ok = true →
      accW acc + pv P * G u ≤ accW (leafAdd c P (tauN (A.sufSet Q n 0) u) pat acc))
    (fuel : ℕ) (hok : (dfsNode c fuel 0 ONE2 1 0 ⟨0, 0, 0, true⟩).ok = true) :
    expect (A.sufSet Q n 0) ν (fun _ => N) G ≤ accW (dfsNode c fuel 0 ONE2 1 0 ⟨0, 0, 0, true⟩) := by
  set S := A.sufSet Q n 0 with hS
  let V : ℕ → (ℕ → ℕ) → ℝ := A.nodeVal Q n ν (fun _ => N) G
  let I : ℕ → (ℕ → ℕ) → ℕ → ℕ → Prop := fun j u τ pat =>
    j ≤ n ∧ (∀ i, j ≤ i → i < n → u (Q i) = 0) ∧ (∀ i < j, u (Q i) ≤ c.acut[i]!) ∧
      τ = tauN S u ∧ pat = ∑ i ∈ range j, min (u (Q i)) (kkf i) * sp i
  have hQS : ∀ j < n, Q j ∈ S := fun j hj => A.mem_sufSet.2 ⟨j, ⟨Nat.zero_le j, hj⟩, rfl⟩
  have hQne : ∀ i j, i < n → j < n → i ≠ j → Q i ≠ Q j := fun i j hi hj hij h =>
    hij (hinj (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj) h)
  have main := dfs_sound c Q N (fun j a => rho (Q j) (ν (Q j)) N a) V I
    -- hstep
    (fun j u τ pat a hj hI ha => by
      rw [hn] at hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI
      refine ⟨by omega, fun i hi1 hi2 => ?_, fun i hi => ?_, ?_, ?_⟩
      · rw [Function.update_of_ne (hQne i j hi2 hj (by omega))]
        exact h2 i (by omega) hi2
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · rw [Function.update_of_ne (hQne i j (by omega) hj (by omega))]
          exact h3 i hi
        · rw [Function.update_self]; exact ha
      · rw [h4, tauN_update_of_mem (hQS j hj) (h2 j le_rfl hj)]
      · rw [h5, sum_range_succ, Function.update_self, hkk j hj, hstride j hj]
        congr 1
        refine sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (hQne i j (by simp at hi; omega) hj (by simp at hi; omega))])
    -- hleaf
    (fun j u τ pat P acc hj hI hok => by
      rw [hn] at hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI
      have hjn : j = n := by omega
      subst hjn
      have hV : V j u = G u := A.nodeVal_of_le le_rfl u
      rw [hV]
      rw [h4] at hok ⊢
      exact hleaf u pat P acc h3 h5 hok)
    -- hsplit
    (fun j u τ pat hj hI => by
      rw [hn] at hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI
      show A.nodeVal Q n ν (fun _ => N) G j u = _
      rw [A.nodeVal_eq_expVal hinj hj (h2 j le_rfl hj)]
      unfold A.expVal
      rw [range_eq_Ico])
    -- hprune
    (fun j u τ pat a P hj hI ha => by
      rw [hn] at hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := hI
      have hE := A.expVal_le (γ := fun _ => N) hinj hq1 hν hC hG0 hG hj
        (fun i hi1 hi2 => h2 i (le_trans (by omega) hi1) hi2) a
      unfold A.expVal at hE
      simp only at hE
      rw [← h4] at hE
      have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
      have hM0 : 0 ≤ hMass (Q j) (ν (Q j)) N a := A.hMass_nonneg (hν j hj).1 (hν j hj).2 N a
      have hX0 : 0 ≤ C * ∏ q ∈ A.sufSet Q n (j + 1), (1 + ν q / ((q : ℝ) - 1)) := by
        refine mul_nonneg hC (prod_nonneg fun q hq => ?_)
        obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := A.mem_sufSet.1 hq
        have := hq1 i hi2
        have h0 := (hν i hi2).1
        have : (1 : ℝ) < Q i := by exact_mod_cast this
        have : 0 ≤ ν (Q i) / ((Q i : ℝ) - 1) := div_nonneg h0 (by linarith)
        linarith
      have hPh : pv P * pv (c.h[j]!)[a]! ≤ pv (mulUp P (c.h[j]!)[a]!) := pv_mul_le_mulUp' _ _
      have hPhR : pv (mulUp P (c.h[j]!)[a]!) * wv c.REW[j + 1]! ≤
          wv (mulUp (mulUp P (c.h[j]!)[a]!) c.REW[j + 1]!) := pv_mul_wv_le_mulUp _ _
      rw [wv_natMul]
      have hP0 := pv_nonneg' P
      have hh' := hh j hj a ha
      have hR' := hREW j hj
      calc pv P * ∑ a' ∈ Ico a (N + 1), rho (Q j) (ν (Q j)) N a' * V (j + 1)
              (Function.update u (Q j) a')
          ≤ pv P * ((τ : ℝ) * hMass (Q j) (ν (Q j)) N a *
              (C * ∏ q ∈ A.sufSet Q n (j + 1), (1 + ν q / ((q : ℝ) - 1)))) :=
            mul_le_mul_of_nonneg_left hE hP0
        _ ≤ (τ : ℝ) * (pv P * pv (c.h[j]!)[a]! * wv c.REW[j + 1]!) := by
            have : hMass (Q j) (ν (Q j)) N a *
                (C * ∏ q ∈ A.sufSet Q n (j + 1), (1 + ν q / ((q : ℝ) - 1))) ≤
                pv (c.h[j]!)[a]! * wv c.REW[j + 1]! :=
              mul_le_mul hh' hR' hX0 (pv_nonneg' _)
            nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hP0 hτ0)]
        _ ≤ (τ : ℝ) * wv (mulUp (mulUp P (c.h[j]!)[a]!) c.REW[j + 1]!) := by
            refine mul_le_mul_of_nonneg_left ?_ hτ0
            exact (mul_le_mul_of_nonneg_right hPh (wv_nonneg _)).trans hPhR)
    -- hρ
    (fun j a hj ha => hρ j (hn ▸ hj) a ha)
    -- hacut
    (fun j hj => hacut j (hn ▸ hj))
    -- hV0
    (fun j u τ pat _ => A.nodeVal_nonneg hν hG0 j u)
  have hI0 : I 0 0 1 0 := by
    refine ⟨Nat.zero_le n, fun i _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i), ?_, by simp⟩
    unfold tauN
    simp
  have h := (main fuel).1 0 0 1 0 ONE2 ⟨0, 0, 0, true⟩ hI0 hok
  have hV0 : V 0 0 = expect S ν (fun _ => N) G := A.nodeVal_zero
  have hacc0 : accW ⟨0, 0, 0, true⟩ = 0 := by simp [accW, wv]
  have hONE : pv ONE2 = 1 := by
    unfold pv; rw [ONE2_eq, ONE_real']; norm_num
  rw [hV0, hacc0, hONE, zero_add, one_mul] at h
  exact h

end MinModulus.Checker2Sound.D
