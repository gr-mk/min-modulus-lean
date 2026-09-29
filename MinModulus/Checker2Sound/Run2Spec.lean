import MinModulus.Checker2Sound.Defs

/-!
# `Checker2Sound.Run2Spec`: the statement of the generic soundness theorem `run2_sound` (L2-E)

STATUS: definitions only. Owned by L2-E. **STABLE** (other agents, in particular
L2-T, may import this file; it imports only `Checker2Sound.Defs`).

`run2_sound` (proved in `Checker2Sound/Assembly.lean`, namespace `MinModulus.Checker2Sound.E`)
says: for every parameter set `P` satisfying the decidable side conditions `SideOK2 P`, a run
with `(run2 P).ok = true` yields every field of `Main.Cert P.m P.X δ₀ c₀ T₀` except the final
numeric inequality (`Run2Facts P`), for the data
* `δ₀ = delta2 P` (`= CheckerMath.deltaPairR (deltaCert2 P)`),
* `c₀ p = pv (costOf2 (run2 P) P p)` (`pv x = x / 2^62`),
* `T₀ = pv (run2 P).T`,
with `Σ_{p ≤ X} c₀ p ≤ pv (etaA + etaB + etaC)`. A later target (another `m`, `X`, schedule, …,
and another tail bound) needs only a new `native_decide` for its own final inequality, plus
`SideOK2 P` by `decide`.

`SideOK2` collects what `run2` does not check at run time:
* `1 ≤ KH`, `1 ≤ TS` (the initial `T_H` and `τ_s` states, `HValid_init`, `TauSValid_init`);
* `5 ≤ m` (then every prime with `N1 = ⌈m/p⌉ ≤ 2` is `≥ 3`, as the e-law needs, also for the
  first-moment primes, which `run2` does not guard);
* `kps[0] ≤ PX` (with the run-time guard `kps[last] ≤ PX`, the δ schedule is constant on
  `(PX, X]` also when the knots are not sorted).
Everything else (`PX ≤ X`, `m ≤ PX`, `2^27 ≤ X`, the schedule guard, …) is part of `(run2 P).ok`.
-/

namespace MinModulus.Checker2Sound.E

open Finset MinModulus.CheckerImpl MinModulus.Checker2Impl MinModulus.CheckerMath MinModulus.Main

/-- The side conditions of `run2_sound` (not checked by `run2` at run time; decidable). -/
def SideOK2 (P : Params2) : Prop :=
  1 ≤ P.KH ∧ 1 ≤ P.TS ∧ 5 ≤ P.m ∧ P.kps[0]! ≤ P.PX

instance (P : Params2) : Decidable (SideOK2 P) :=
  inferInstanceAs (Decidable (1 ≤ P.KH ∧ 1 ≤ P.TS ∧ 5 ≤ P.m ∧ P.kps[0]! ≤ P.PX))

/-- **What `run2_sound` delivers** for a successful run: every field of
`Main.Cert P.m P.X (delta2 P) c₀ T₀` except `total_lt`, where
`c₀ p = pv (costOf2 (run2 P) P p)`, `T₀ = pv (run2 P).T`, and the sum of the costs is bounded by
`pv (etaA + etaB + etaC)`. -/
structure Run2Facts (P : Params2) : Prop where
  two_pow_le : 2 ^ 27 ≤ P.X
  delta_nonneg : ∀ p, p.Prime → 0 ≤ delta2 P p
  delta_le_half : ∀ p, p.Prime → delta2 P p ≤ 1 / 2
  delta_tail : ∀ p, p.Prime → P.X < p → delta2 P p = 1 / 2
  loss_le : ∀ p, p.Prime → p ≤ P.X → ∀ N : ℕ,
    hingeLoss P.m (delta2 P) p (fun _ => N) ≤ pv (costOf2 (run2 P) P p)
  sum_le : ∑ p ∈ Nat.primesLE P.X, pv (costOf2 (run2 P) P p) ≤
    pv ((run2 P).etaA + (run2 P).etaB + (run2 P).etaC)
  prod_le : ∏ q ∈ Nat.primesLE P.X, tailFactor (delta2 P) q ≤ pv (run2 P).T

/-- The statement of `run2_sound`, as a proposition (for agents that want to take it as a
hypothesis before `Checker2Sound/Assembly.lean` is finished). -/
def Run2SoundStmt : Prop :=
  ∀ P : Params2, SideOK2 P → (run2 P).ok = true → Run2Facts P

end MinModulus.Checker2Sound.E
