import MinModulus.Checker2Sound.Defs
import MinModulus.Checker2Sound.Assembly
import MinModulus.Checker2Sound.StatesH
import MinModulus.Checker2Sound.StatesTauS
import MinModulus.Checker2Sound.StatesE
import MinModulus.Checker2Sound.Tables
import MinModulus.Checker2Sound.SBHSound
import MinModulus.Checker2Sound.Split
import MinModulus.Checker2Impl.Certificate
import MinModulus.Main.Main

/-!
# `Checker2Sound.Interfaces`: the stage-2 contract of the second soundness proof

STATUS (stage 2, complete): all ten statements below are proved; each forwards to its owner's
theorem `MinModulus.Checker2Sound.{B,C,D}.<same name>` (axioms `propext`, `Classical.choice`,
`Quot.sound`). The loop, the block phase and the assembly (L2-E: `Checker2Sound/Loop*.lean`,
`Assembly.lean`) take the eight statements used by the loops as one hypothesis `E.Stage2Stmts`
(`LoopStmts.lean`, verbatim copies). At the end of this file: `stage2Stmts` (the bundle),
`E.run2_sound` and `E.cert_of_run2` (generic in the parameters), `cert_14600` and the final theorem
`not_covers_14600`, whose axioms are the three standard ones and the `native_decide` axiom of
`Checker2Impl.check2_eq_true` (`AssemblyAudit.lean`). Not imported by the default target
`MinModulus`; nothing in the existing development depends on this file. Owned by the assembly agent
(L2-E). See `SCRATCH/agents/lean2/LEAN2_DESIGN.md` §6 and `STAGE2_HUB.md`.

## Protocol (as in the first proof, `CheckerSound/Interfaces.lean`)
1. Prove **exactly** the statement you own, in your own files and namespace, **with the same
   name**: `MinModulus.Checker2Sound.C.HValid_extend`, `…D.sbhCost_sound`, … .
2. Import `MinModulus.Checker2Sound.Defs` (+ Checker2Math / CheckerMath / Checker2Impl / Mathlib),
   never this file. Changes to `Defs.lean` go through L2-E.
3. If a statement is false or inconvenient, do not silently change it: propose the change in your
   file header and tell L2-E.
4. No placeholder proofs, no `native_decide`, no new axioms; allowed: `propext`, `Classical.choice`,
   `Quot.sound`.

## Owners
* **L2-C** (code primitives and DP states, `Checker2Sound/Prims*`, `States*`, `Tables*`):
  `HValid_init`, `HValid_extend`, `TauSValid_init`, `TauSValid_add`, `ELawValid_init`,
  `ELawValid_add`, `buildTab_sound`.
* **L2-D** (the S/B/H cost, `Checker2Sound/SBH*`): `sbhCost_sound` (math from L2-A,
  `Checker2Math/SBHLaw*`).
* **L2-B** (the τ-split cost, `Checker2Math/SplitLaw*`, `Checker2Sound/Split*`): `splitCost_sound`.
* **L2-E** (loop, blocks, assembly, `Checker2Sound/Loop*`, `Assembly*`, this file): `cert_14600`.
-/

namespace MinModulus.Checker2Sound

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath
  MinModulus.Checker2Math MinModulus.Main MinModulus.Smooth

/-! ## L2-C: DP states and tables -/

/-- **(L2-C)** The empty `T_H` state. -/
theorem HValid_init (P : Params2) (hKH : 1 ≤ P.KH) : HValid P (HState.init P.KH) :=
  C.HValid_init P hKH

/-- **(L2-C)** `HState.extend` makes `H = primes2 P [iN1:k]` (code: `HState.addRange`,
`lawStepFull`, `pmArr`, `facE1u`; math: `TauLaw.lawTau_insert`, `rho_eq_pointMass`). -/
theorem HValid_extend (P : Params2) (hPX : P.PX ≤ P.X) {H : HState} (hH : HValid P H) {iN1 k : ℕ}
    (hk : k ≤ (primes2 P).size) (hiN1 : iN1 < k)
    (hok : (H.extend (primes2 P) (dns2 P) P.KH iN1 k).2 = true) :
    HValid P (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1 ∧
      (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1.lo = iN1 ∧
      (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1.hi = k :=
  C.HValid_extend P hPX hH hk hiN1 hok

/-- **(L2-C)** The empty weighted `τ_s` state. -/
theorem TauSValid_init (P : Params2) (hTS : 1 ≤ P.TS) : TauSValid P (TauSState.init P.TS) ∅ :=
  C.TauSValid_init P hTS

/-- **(L2-C)** Adding a prime to the weighted `τ_s` DP (code: `dpRange`, `weightByTau`, `pmArr`,
`lostSumW`, `hArr`, `facE1u`; math: `TauLaw.lawKept_insert_le`, `lostMass_insert_le`,
`expect1_hA_le`, `expect1_add_one_le`, times the weight `T`). -/
theorem TauSValid_add (P : Params2) {st : TauSState} {S : Finset ℕ} (h : TauSValid P st S)
    {q : ℕ} (hq : q.Prime) (hqX : q ≤ P.X) (hqS : q ∉ S) :
    TauSValid P (st.add P.TS q (deltaN2 P q)) (insert q S) :=
  C.TauSValid_add P h hq hqX hqS

/-- **(L2-C)** The empty weighted e-law. -/
theorem ELawValid_init (P : Params2) : ELawValid P (ELaw.init P.NN) ∅ :=
  C.ELawValid_init P

/-- **(L2-C)** Adding a number `q ≥ 3` to the weighted e-law (code: `eOuter`, `eInner`,
`weightByPow2`, `pmArr`, `h2Up`, `e2Up`; math: the e-law recursion of L2-B). -/
theorem ELawValid_add (P : Params2) {el : ELaw} {L : Finset ℕ} (h : ELawValid P el L) {q : ℕ}
    (hq : 3 ≤ q) (hqX : q ≤ P.X) (hqL : q ∉ L) :
    ELawValid P (el.add P.NN q (deltaN2 P q)) (insert q L) :=
  C.ELawValid_add P h hq hqX hqL

/-- **(L2-C → L2-D)** The lower-tail table of one profile. With `R = B ∪ H` (`B` = the primes of
`Bq`, `H = idxSet P H.lo H.hi`, disjoint) and the profile `a` (`profileFn Bq a`, zero off `B`),
for every cap `N ≥ KH`:
* `bm = Σ a` and `E[b] ≥ wv EbW`;
* for every row `b ≤ bm` and every real `c ≥ 0` with `⌊c⌋ ≤ K`:
  `Σ_{j ≤ ⌊c⌋} (c − j)·P(T = j ∧ b) ≤ c·pv S0[b][⌊c⌋] − wv S1W[b][⌊c⌋]`
(code: `buildTab`, `rowsAll`, `rowsStep`, `dpRange`, `prefixTables`, `ebLoW`; math: the
`lawJoint` recursion of L2-A). -/
theorem buildTab_sound (P : Params2) (hPX : P.PX ≤ P.X) {H : HState} (hH : HValid P H)
    {Bq Bdn a : Array ℕ}
    (hBq : ∀ q ∈ Bq.toList, q.Prime ∧ q ≤ P.X) (hBnd : Bq.toList.Nodup)
    (hBH : Disjoint Bq.toList.toFinset (idxSet P H.lo H.hi))
    (hBdn : Bdn = Bq.map (deltaN2 P)) (ha : a.size = Bq.size) (tp1int : ℕ) (N : ℕ)
    (hN : P.KH ≤ N) :
    let tab := buildTab a Bq Bdn ((Array.range Bq.size).map fun i =>
      pmArr Bq[i]! Bdn[i]! (P.KH - 1)) H.D P.KH tp1int
    let R := Bq.toList.toFinset ∪ idxSet P H.lo H.hi
    tab.bm = a.foldl (· + ·) 0 ∧
      wv tab.EbW ≤ ∑ q ∈ Bq.toList.toFinset, (profileFn Bq a q : ℝ) * (nu2 P q / q) ∧
      ∀ b, b ≤ tab.bm → ∀ c : ℝ, 0 ≤ c → ⌊c⌋₊ ≤ tab.K →
        ∑ j ∈ range (⌊c⌋₊ + 1), (c - j) * lawJoint R (profileFn Bq a) (nu2 P) (fun _ => N) j b ≤
          c * pv (tabS0 tab b ⌊c⌋₊) - wv (tabS1W tab b ⌊c⌋₊) :=
  C.buildTab_sound P hPX hH hBq hBnd hBH hBdn ha tp1int N hN

/-! ## L2-D: the S/B/H cost -/

/-- **(L2-D)** Soundness of the S/B/H cost at the prime `p = primes2 P [k]` with `N1 ≥ 3`, given a
valid `T_H` state (the run-time guard `ok` checks that `H` is the set `[N1, p)`), for every cap `N`.
(Math: `Checker2Math.hingeLoss_eq_sbh`, the small-pattern lemmas, the lower-tail identity, the
`lawJoint` and DFS lemmas of L2-A; code: `patternData`, `smallDivs`, `cdTable`, `corrSum`,
`leafValue`, `dfsNode`/`dfsExp`, `buildTab_sound`.) -/
theorem sbhCost_sound (P : Params2) (hPX : P.PX ≤ P.X) {k : ℕ} (hk : k < (primes2 P).size)
    (hN1 : 3 ≤ cdiv P.m (primes2 P)[k]!) {H : HState} (hH : HValid P H)
    (hok : (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).ok = true) (N : ℕ) :
    hingeLoss P.m (delta2 P) (primes2 P)[k]! (fun _ => N) ≤
      pv (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).cost :=
  D.sbhCost_sound P hPX hk hN1 hH hok N

/-! ## L2-B: the τ-split cost (per prime and per block) -/

/-- **(L2-B)** Soundness of the τ-split cost evaluated at `B ≤ p` (`B = p` in the per-prime phase;
`B` = the block start, `m ≤ B`, in the block phase), for a prime `p ≤ X` with `m ≤ 2B`, the same δ
at `B` and `p`, a valid weighted `τ_s` state for `S` and a valid e-law for `L`, where `S` and `L`
are disjoint and cover the primes below `p` (`L` may contain extra numbers: monotone coupling).
(Math: `Checker2Math.hingeLoss_eq_tauSplit`, `hinge_tau_split_le`,
`card_divisors_smooth_le_two_pow`, Fubini `Smooth.expect_union`, the e-law and weighted-suffix
lemmas of L2-B; code: `splitCost`, `splitVal`, `gsUp`, `splitThreshold`, `TauSState.freeze`,
`suffixTablesW`.) -/
theorem splitCost_sound (P : Params2) {st : TauSState} {S : Finset ℕ} (hS : TauSValid P st S)
    {el : ELaw} {L : Finset ℕ} (hL : ELawValid P el L) (hSL : Disjoint S L) {p B : ℕ}
    (hp : p.Prime) (hB2 : 2 ≤ B) (hBp : B ≤ p) (hBp' : B = p ∨ P.m ≤ B) (hpX : p ≤ P.X)
    (hm : P.m ≤ 2 * B) (hsub : Nat.primesBelow p ⊆ S ∪ L) (hdn : deltaN2 P B = deltaN2 P p)
    (N : ℕ) :
    hingeLoss P.m (delta2 P) p (fun _ => N) ≤
      pv (splitCost P.m P.NN B (deltaN2 P B) (st.freeze P.TS) el) :=
  MinModulus.Checker2Sound.B.splitCost_sound P hS hL hSL hp hB2 hBp hBp' hpX hm hsub hdn N

/-! ## L2-E: loop, blocks and assembly (proved in `Checker2Sound/Loop*.lean`, `Assembly.lean`) -/

/-- The eight statements above that the loops of `run2` use, bundled (`E.Stage2Stmts`). -/
theorem stage2Stmts : E.Stage2Stmts :=
  ⟨HValid_init, HValid_extend, TauSValid_init, TauSValid_add, ELawValid_init, ELawValid_add,
    sbhCost_sound, splitCost_sound⟩

/-- **(L2-E) Soundness of a successful run of the second checker**, for any parameters with the
decidable side conditions `E.SideOK2` (`Run2Spec.lean`): every field of
`Main.Cert P.m P.X (delta2 P) c₀ T₀` except the final numeric inequality (`E.Run2Facts`), with
`c₀ p = pv (costOf2 (run2 P) P p)`, `T₀ = pv (run2 P).T`, `Σ c₀ ≤ pv (etaA + etaB + etaC)`. -/
theorem E.run2_sound (P : Params2) (hP : E.SideOK2 P) (hok : (run2 P).ok = true) :
    E.Run2Facts P :=
  E.run2_sound_of stage2Stmts P hP hok

/-- **(L2-E)** The certificate from a successful check, for any parameters with `E.SideOK2`. -/
theorem E.cert_of_run2 (P : Params2) (hP : E.SideOK2 P) (hchk : checkWith2 P = true) :
    Cert P.m P.X (delta2 P) (fun p => pv (costOf2 (run2 P) P p)) (pv (run2 P).T) :=
  E.cert_of_run2_of stage2Stmts P hP hchk

/-- **(L2-E)** The numeric certificate for `m = 14600`, `X = 2·10^8`: `check2_eq_true`
(`native_decide`), `checkWith2_spec`, `E.run2_sound` (the loop invariants of `run2` and the
statements above, `CheckerMath.hingeLoss_le_firstMoment_impl` for `p < 17`, the block phase with
`CheckerSound.A.sieve_get_prime`), and `CheckerMath.cert_of_check`. -/
theorem cert_14600 : ∃ (δ c : ℕ → ℝ) (T : ℝ), Cert 14600 (2 * 10 ^ 8) δ c T :=
  E.cert_14600_of stage2Stmts

/-- **Theorem.** Congruences `a i (mod d i)` with distinct moduli `d i ≥ 14600` do not cover `ℤ`:
every covering system with distinct moduli has least modulus `≤ 14599`. -/
theorem not_covers_14600 {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : Function.Injective d) (hm : ∀ i, 14600 ≤ d i) :
    ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i) := by
  obtain ⟨δ, c, T, hc⟩ := cert_14600
  exact Main.not_covers_of_cert hc (by norm_num) d a hd hm

end MinModulus.Checker2Sound
