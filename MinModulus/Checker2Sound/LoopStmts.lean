import MinModulus.Checker2Sound.Defs

/-!
# `Checker2Sound.LoopStmts`: the stage-2 statements used by the loop, as one proposition (L2-E)

STATUS: definitions only. Owned by L2-E. **STABLE** (imports only `Defs`).

`Stage2Stmts` bundles, **verbatim**, the eight statements of `Checker2Sound/Interfaces.lean` that the
prime loop, the block phase and the assembly use (`HValid_init`, `HValid_extend`,
`TauSValid_init`, `TauSValid_add`, `ELawValid_init`, `ELawValid_add` (L2-C), `sbhCost_sound`
(L2-D), `splitCost_sound` (L2-B); `buildTab_sound` is used only inside L2-D's proof).
`E.run2_sound_of (h : Stage2Stmts)` (`Assembly.lean`) is proved from this hypothesis, so that its
`#print axioms` shows that everything else is proved; `MinModulus.Checker2Sound.stage2Stmts` (in
`Interfaces.lean`) collects the owners' theorems, and `E.run2_sound` (also there) is the instance.
Any accepted change of one of these statements in `Interfaces.lean` is mirrored here by L2-E.
-/

namespace MinModulus.Checker2Sound.E

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath MinModulus.Main

/-- The eight stage-2 statements used by the loops of `run2` (verbatim from `Interfaces.lean`). -/
structure Stage2Stmts : Prop where
  HValid_init : ∀ (P : Params2), 1 ≤ P.KH → HValid P (HState.init P.KH)
  HValid_extend : ∀ (P : Params2), P.PX ≤ P.X → ∀ {H : HState}, HValid P H → ∀ {iN1 k : ℕ},
    k ≤ (primes2 P).size → iN1 < k → (H.extend (primes2 P) (dns2 P) P.KH iN1 k).2 = true →
    HValid P (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1 ∧
      (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1.lo = iN1 ∧
      (H.extend (primes2 P) (dns2 P) P.KH iN1 k).1.hi = k
  TauSValid_init : ∀ (P : Params2), 1 ≤ P.TS → TauSValid P (TauSState.init P.TS) ∅
  TauSValid_add : ∀ (P : Params2) {st : TauSState} {S : Finset ℕ}, TauSValid P st S →
    ∀ {q : ℕ}, q.Prime → q ≤ P.X → q ∉ S →
    TauSValid P (st.add P.TS q (deltaN2 P q)) (insert q S)
  ELawValid_init : ∀ (P : Params2), ELawValid P (ELaw.init P.NN) ∅
  ELawValid_add : ∀ (P : Params2) {el : ELaw} {L : Finset ℕ}, ELawValid P el L →
    ∀ {q : ℕ}, 3 ≤ q → q ≤ P.X → q ∉ L →
    ELawValid P (el.add P.NN q (deltaN2 P q)) (insert q L)
  sbhCost_sound : ∀ (P : Params2), P.PX ≤ P.X → ∀ {k : ℕ}, k < (primes2 P).size →
    3 ≤ cdiv P.m (primes2 P)[k]! → ∀ {H : HState}, HValid P H →
    (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).ok = true → ∀ (N : ℕ),
    hingeLoss P.m (delta2 P) (primes2 P)[k]! (fun _ => N) ≤
      pv (sbhCost P (primes2 P)[k]! (dns2 P)[k]! (primes2 P) (dns2 P) k H).cost
  splitCost_sound : ∀ (P : Params2) {st : TauSState} {S : Finset ℕ}, TauSValid P st S →
    ∀ {el : ELaw} {L : Finset ℕ}, ELawValid P el L → Disjoint S L → ∀ {p B : ℕ},
    p.Prime → 2 ≤ B → B ≤ p → (B = p ∨ P.m ≤ B) → p ≤ P.X → P.m ≤ 2 * B →
    Nat.primesBelow p ⊆ S ∪ L → deltaN2 P B = deltaN2 P p → ∀ (N : ℕ),
    hingeLoss P.m (delta2 P) p (fun _ => N) ≤
      pv (splitCost P.m P.NN B (deltaN2 P B) (st.freeze P.TS) el)

end MinModulus.Checker2Sound.E
