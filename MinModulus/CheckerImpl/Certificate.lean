import MinModulus.CheckerImpl.Checker
/-
# `MinModulus.CheckerImpl.Certificate` — the checked Bool for `m = 16000`, `X = 2·10^8`

Status: complete, no `sorry`. Core Lean only. This module is **not** precompiled (it is in the
Lake library `CheckerCert`); it imports the precompiled library `CheckerImpl`, so
`native_decide` below runs the checker as native code.

`check_eq_true` depends on the axioms `propext`, `Classical.choice`, `Quot.sound` and the
auxiliary axiom that Lean 4.34's `native_decide` introduces for the evaluated Bool
(`check_eq_true._native.native_decide.ax_…`).

## Certificate data (to be used by the soundness proof; `P := fullParams`, `r := run P`)
* `δ₀ p := (deltaCert P p).1 / (deltaCert P p).2` — `deltaN P p / 10^9` for `p ≤ X`, `1/2` for
  `p > X`. (`0 ≤ δ₀ ≤ 0.45` on `p ≤ X` by the clamp in `deltaN`.)
* `c₀ p := costOf r P p / 2^62`.
* `T₀ := r.T / 2^62`.

## Lemma target for "the Bool is true → the real inequality holds"
```
check = true →
  (∑ p ∈ Nat.primesLE X, (costOf r P p : ℝ) / 2^62) + ((r.T : ℝ) / 2^62) * (100 / (189 * X)) < 1
```
Proof sketch: `check = true` gives `r.ok = true` and `r.etaA + r.etaB + r.etaC + tailUp P r.T < 2^62`.
* `r.etaA + r.etaB = Σ_{p ≤ PX prime} r.costs[p]` (each prime `p ≤ PX` adds its cost once and
  stores it in `costs[p]`; `primesUpTo PX` is exactly the primes `≤ PX`);
* `r.etaC = Σ_blocks b.count · b.val ≥ Σ_{PX < p ≤ X prime} costOf r P p`, because the blocks
  `[start, stop)` partition `(PX, X]` and `b.count = countUnmarked (sieve X) start stop` is `≥` the
  number of primes in the block (the sieve only marks products `i·(i+r)`, `i ≥ 2`);
* `tailUp P T = ⌈T·100/(189 X)⌉ ≥ T·100/(189 X)` (P-values).
-/
namespace MinModulus.CheckerImpl

/-- The checked Bool for the final configuration (`m = 16000`, `X = 2·10^8`). -/
def check : Bool := checkWith fullParams

/-- The numeric certificate, evaluated by native code. -/
theorem check_eq_true : check = true := by native_decide

end MinModulus.CheckerImpl
