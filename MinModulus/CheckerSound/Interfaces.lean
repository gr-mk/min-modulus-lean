import MinModulus.CheckerSound.Defs
import MinModulus.CheckerSound.Blocks
import MinModulus.CheckerSound.Sieve
import MinModulus.CheckerSound.TauDP
import MinModulus.CheckerSound.CompCost

/-!
# `CheckerSound.Interfaces`: the statements CS-D needs from CS-A, CS-B and CS-C

STATUS (CS-D): complete, no `sorry`. All 8 statements are proved by their owners and wired below
(CS-A: `Sieve.lean`, `Blocks.lean`; CS-B: `TauDP.lean`; CS-C: `CompCost.lean`); each depends only on
`propext`, `Classical.choice`, `Quot.sound`. CS-D's loop and assembly use `comparisonCost_sound`
through the proposition `ComparisonCostSound` (end of this file); `CheckerSound/Audit.lean` prints
the axioms of the final theorem. Owned by CS-D (assembly).
The vocabulary (`pv`, `delta0`, `acutA`, `acutB`, `BValid`, `AValid`, `blockPhase`, `blockCost`,
`BlockHyp`, `ETHyp`) is in `CheckerSound/Defs.lean`; read its header first.

## Protocol (please follow it exactly)
1. Prove **exactly** the statement below that you own, in your own file(s)
   (`CheckerSound/Blocks*|Sieve*|FirstMomentCode*|MomentCode*` for CS-A, `CheckerSound/TauDP*` for
   CS-B, `CheckerSound/Enum*|CompCost*` for CS-C), in your namespace, **with the same name**:
   `MinModulus.CheckerSound.A.blockPhase_T_le`, `MinModulus.CheckerSound.B.BValid_addPrime`,
   `MinModulus.CheckerSound.C.comparisonCost_sound`, … .
2. Your files import `MinModulus.CheckerSound.Defs` (plus CheckerMath / CheckerImpl / Mathlib),
   **never this file** (this file will import yours: no cycles). No agent needs another agent's
   statement: CS-C receives `AValid`/`BValid` as hypotheses; CS-D combines everything.
3. If a statement is false or inconvenient as written, do not silently change it: write the
   proposed change in your file header and tell CS-D. Changes to `Defs.lean` go through CS-D.
4. When you are done, report the name and file; CS-D replaces the `sorry` here by your theorem.
5. No `sorry`, `admit`, `native_decide` or new axioms in your proofs; allowed axioms:
   `propext`, `Classical.choice`, `Quot.sound`.

## How CS-D uses them (for orientation; `P := fullParams`, `r := run P`)
* δ of the certificate `delta0 P`; costs `c₀ p = pv (costOf r P p)`; `T₀ = pv r.T`.
* Prime loop (`primeLoop`, CS-D): for the prime `p = primes[k] ≤ PX`, `dn = deltaN P p`:
  - `dn = 0` (then all smaller primes have `dn = 0`, flag `allZero`):
    `costs[p] = firstMoment P.m p (primes.extract 0 k)` → `CheckerMath.hingeLoss_le_firstMoment_impl`
    (ImplBridge; CS-D applies it, nothing to do for CS-A);
  - `dn > 0`: `costs[p] = (comparisonCost P p dn aps adns A B).cost` with `aps = primes[0:nAz]`
    (= the primes below `z := primes[nAz]`), `adns = aps.map (deltaN P)`,
    `A = buildA aps adns KMAX` (`buildA_valid`, CS-B) and `B` the B-state of the primes in
    `[z, p)` (built by `BState.init` and `BState.addPrime` in some order: `BValid_init`,
    `BValid_addPrime`, CS-B) → `comparisonCost_sound` (CS-C).
  - CS-D proves `etaA + etaB = Σ_{p ≤ PX prime} costs[p]` and `ETHyp P ET2 ET25 ET3` for the
    running products after the loop (`primesUpTo_toList`, CS-A, gives the list of primes).
* Block phase (`blockLoop`, CS-A): `blockPhase_cost_sound` (loss at `PX < p ≤ X`),
  `blockPhase_sum_le` (`etaC` bounds the block costs), `blockPhase_T_le` (`r.T` bounds
  `∏_{q ≤ X} tailFactor`), with `dC = 409200000` for `fullParams`.
* Then `CheckerMath.cert_of_check` + `checkWith_spec` + `check_eq_true` give `cert_16000`.

## Math already available (use it, do not reprove it)
* `CheckerMath/ImplBridge.lean` (verified): `hingeLoss_le_blockVal` (per-prime value of a block),
  `expect1_sq_le_fac2`, `expect1_cube_le_fac3`, `expect1_five_halves_le_fac25`, `tailFactor_le_fac2`
  (per-prime factors, block form `Q ≤ q`), `ratUp_ge`, `cdiv_ge`, `mulUp_ge`,
  `hingeLoss_le_firstMoment_impl`. `Defs.lean` does not import it (to avoid name clashes with
  files already written); import `MinModulus.CheckerMath.ImplBridge` yourself.
* `CheckerMath/ComparisonBound.lean`: `hingeLoss_le_of_comparison` and the function→lemma table.
* `CheckerMath/Glue.lean`: `sum_primesLE_le_split`, `prod_primesLE_le_split`, `sum_le_of_cover`,
  `prod_le_of_cover`, `sum_primesBelow_le_add`, `prod_primesBelow_le_mul_pow`.

## Notes on the statements
* All statements are for a general `P : Params` with explicit hypotheses (CS-D discharges them
  for `fullParams`); no evaluation of `fullParams` is needed in your proofs.
* `N ≥ 65` inside `AValid`/`BValid` (every `acut ≤ 64`); the final conclusions are for **every**
  cap `N` (lift with `CheckerMath.hingeLoss_le_of_comparison` / `hingeLoss_le_of_forall_ge`).
* `x[i]!` is `getElem!` (the code's reads); `pv x = x / 2^62`.
-/

namespace MinModulus.CheckerSound

open Finset MinModulus.CheckerImpl MinModulus.CheckerMath MinModulus.Main

/-! ## CS-A: primes and blocks -/

/-- **(CS-A, Primes)** `primesUpTo n` is the increasing list of the primes `≤ n`
(`isPrimeTD` is exact trial division). -/
theorem primesUpTo_toList (n : ℕ) :
    (primesUpTo n).toList = (List.range (n + 1)).filter (fun q => decide q.Prime) :=
  MinModulus.CheckerSound.A.primesUpTo_toList n

/-- **(CS-A, block costs)** Every prime `p ∈ (PX, X]` has hinge loss at most the `val` of its
block, for every uniform cap `N`, when the block phase starts from running products satisfying
`ETHyp`. What is left for CS-A is the loop: the block containing `p` (found by `find?`), its
`val = blockVal B dC ET2' ET25' ET3'` with `ET_θ'` bounding the product of the per-prime factors
over the primes below `p` (the primes `≤ PX` via `ETHyp`, the earlier blocks and the current
block via `powUp`, `count ≥ #primes`, factors `≥ 1`); then `CheckerMath.hingeLoss_le_blockVal`
with the per-prime bounds `expect1_sq_le_fac2`, `expect1_five_halves_le_fac25`,
`expect1_cube_le_fac3` (`Q = q` for `q ≤ PX`, `Q` = block start otherwise). -/
theorem blockPhase_cost_sound (P : Params) {dC : ℕ} (hP : BlockHyp P dC) {ET2 ET25 ET3 : ℕ}
    (hET : ETHyp P ET2 ET25 ET3) {p : ℕ} (hp : p.Prime) (hlo : P.PX < p) (hhi : p ≤ P.PMAX)
    (N : ℕ) :
    hingeLoss P.m (delta0 P) p (fun _ => N) ≤
      pv (blockCost (blockPhase P ET2 ET25 ET3).blocks p) :=
  MinModulus.CheckerSound.A.blockPhase_cost_sound P hP hET hp hlo hhi N

/-- **(CS-A, block sum)** `etaC` bounds the sum of the block costs over the primes in `(PX, X]`
(the blocks partition `(PX, X]`; `count = countUnmarked (sieve X) start stop ≥ #primes`; every
prime is unmarked by the sieve). (Math layer: `CheckerMath.sum_primesLE_le_split`,
`sum_le_of_cover`.) -/
theorem blockPhase_sum_le (P : Params) {dC : ℕ} (hP : BlockHyp P dC) (ET2 ET25 ET3 : ℕ) :
    ∑ p ∈ (Nat.primesLE P.PMAX).filter (P.PX < ·),
        pv (blockCost (blockPhase P ET2 ET25 ET3).blocks p) ≤
      pv (blockPhase P ET2 ET25 ET3).etaC :=
  MinModulus.CheckerSound.A.blockPhase_sum_le P hP ET2 ET25 ET3

/-- **(CS-A, the T bound)** The final `ET2` bounds `T = ∏_{q ≤ X} tailFactor (delta0 P) q`.
(Per prime: `CheckerMath.tailFactor_le_fac2` with `Q = q` for `q ≤ PX`, `Q` = block start for
the blocks; `prod_primesLE_le_split`, `prod_le_of_cover`, `powUp`.) -/
theorem blockPhase_T_le (P : Params) {dC : ℕ} (hP : BlockHyp P dC) {ET2 ET25 ET3 : ℕ}
    (hET : ETHyp P ET2 ET25 ET3) :
    ∏ q ∈ Nat.primesLE P.PMAX, tailFactor (delta0 P) q ≤ pv (blockPhase P ET2 ET25 ET3).ET2 :=
  MinModulus.CheckerSound.A.blockPhase_T_le P hP hET

/-! ## CS-B: the τ-DP states -/

/-- **(CS-B)** The empty B-part state is valid for `S = ∅` (`τ_∅ = 1`), for `N ≥ 2`.
(Math layer: `CheckerMath.lawKept_empty`.) -/
theorem BValid_init (P : Params) {N : ℕ} (hN : 2 ≤ N) : BValid P (BState.init N) ∅ :=
  MinModulus.CheckerSound.B.BValid_init P hN

/-- **(CS-B)** Adding a prime `q ≤ X` (with its own δ-value `deltaN P q`) to a valid B-part state
for `S ∌ q` gives a valid B-part state for `insert q S`. (Code: `mkExpLaw q dn 60`, `dpStep true`,
`facE1`; math layer: `CheckerMath.lawKept_insert_le`, `rho_eq_pointMass`, `lawKept_congr_cap`.) -/
theorem BValid_addPrime (P : Params) {B : BState} {S : Finset ℕ} (hB : BValid P B S) {q : ℕ}
    (hq : q.Prime) (hqX : q ≤ P.PMAX) (hqS : q ∉ S) :
    BValid P (B.addPrime q (deltaN P q)) (insert q S) :=
  MinModulus.CheckerSound.B.BValid_addPrime P hB hq hqX hqS

/-- **(CS-B)** `buildA` of a duplicate-free array of primes `≤ X` (any order), with their own
δ-values, is a valid A-part state for the set of these primes. (Code: `mkExpLaw q dn 62`,
`dpStep true/false`, `facE1`, `sumK`, `top`; math layer: `CheckerMath.lawKept_insert_le`,
`le_lawKept_insert`, `lostMass_le_of_lower`, `meanTau_le`.) -/
theorem buildA_valid (P : Params) (hK : 1 ≤ P.KMAX) (aps adns : Array ℕ)
    (hnd : aps.toList.Nodup) (hpr : ∀ q ∈ aps.toList, q.Prime ∧ q ≤ P.PMAX)
    (hadns : adns = aps.map (deltaN P)) :
    AValid P (buildA aps adns P.KMAX) aps.toList.toFinset :=
  MinModulus.CheckerSound.B.buildA_valid P hK aps adns hnd hpr hadns

/-! ## CS-C: enumeration and the comparison cost -/

/-- **(CS-C)** Soundness of `comparisonCost` at a prime `p ≤ X` with `δ_p = deltaN P p/10^9 > 0`,
for the partition of the primes below `p` into `A` = the primes below `z` (the array `aps`, in
increasing order, with δ-values `adns`) and `B` = the primes in `[z, p)`: if the run-time guard
`ok` holds, the cost bounds the hinge loss for every uniform cap `N`.
(Math layer: `CheckerMath.hingeLoss_le_of_comparison` with `ν := tilt (delta0 P)`, `N0 = 65`,
`E = {v | smooth A v ≤ enumCutoff P p}`, `KM = KMAX`, `acut = acutA P`; `meanTau_le`,
`expLostProb_le` for `B`; see the table in `CheckerMath/ComparisonBound.lean`.) -/
theorem comparisonCost_sound (P : Params) {p : ℕ} (hp : p.Prime) (hpX : p ≤ P.PMAX)
    (hdn : 0 < deltaN P p) {z : ℕ} (hzp : z ≤ p) (aps adns : Array ℕ)
    (haps : aps.toList = (List.range z).filter (fun q => decide q.Prime))
    (hadns : adns = aps.map (deltaN P)) {A : AState} (hA : AValid P A (Nat.primesBelow z))
    {B : BState} (hB : BValid P B ((Nat.primesBelow p).filter (z ≤ ·)))
    (hok : (comparisonCost P p (deltaN P p) aps adns A B).ok = true) (N : ℕ) :
    hingeLoss P.m (delta0 P) p (fun _ => N) ≤
      pv (comparisonCost P p (deltaN P p) aps adns A B).cost :=
  MinModulus.CheckerSound.C.comparisonCost_sound P hp hpX hdn hzp aps adns haps hadns hA hB hok N

/-- The statement of `comparisonCost_sound` as a proposition. CS-D's loop and assembly take it as
a hypothesis (`Loop.lean`, `Assembly.lean`), so that the audit
`CheckerSound.D.not_covers_of_comparisonCostSound` (in `CheckerSound/Audit.lean`) shows that it is
the only missing piece. -/
def ComparisonCostSound : Prop :=
  ∀ (P : Params) {p : ℕ}, p.Prime → p ≤ P.PMAX → 0 < deltaN P p → ∀ {z : ℕ}, z ≤ p →
    ∀ (aps adns : Array ℕ), aps.toList = (List.range z).filter (fun q => decide q.Prime) →
    adns = aps.map (deltaN P) → ∀ {A : AState}, AValid P A (Nat.primesBelow z) →
    ∀ {B : BState}, BValid P B ((Nat.primesBelow p).filter (z ≤ ·)) →
    (comparisonCost P p (deltaN P p) aps adns A B).ok = true → ∀ N : ℕ,
    hingeLoss P.m (delta0 P) p (fun _ => N) ≤
      pv (comparisonCost P p (deltaN P p) aps adns A B).cost

theorem comparisonCostSound : ComparisonCostSound :=
  fun P _ hp hpX hdn _ hzp aps adns haps hadns _ hA _ hB hok N =>
    comparisonCost_sound P hp hpX hdn hzp aps adns haps hadns hA hB hok N

end MinModulus.CheckerSound
