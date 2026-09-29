# The least modulus of a distinct covering system is at most 14,500 — Lean 4 formalization

This repository is a Lean 4 (v4.34.1) and Mathlib formalization of the main theorem of the paper *The least modulus
of a distinct covering system is at most 14,500* (Grayson MacKenzie). It contains no `sorry`.

**Theorem** (`MinModulus/Checker2Sound/Final14501.lean`). Finitely many congruences a_i (mod d_i) with distinct
moduli d_i ≥ 14,501 do not cover ℤ. So every covering system with distinct moduli has least modulus at most 14,500.

```lean
theorem MinModulus.Checker2Sound.not_covers_14501 {ι : Type*} [Fintype ι] (d : ι → ℕ) (a : ι → ℤ)
    (hd : Function.Injective d) (hm : ∀ i, 14501 ≤ d i) :
    ∃ x : ℤ, ∀ i, ¬ ((d i : ℤ) ∣ x - a i)
```

Previously, Balister, Bollobás, Morris, Sahasrabudhe and Tiba had shown that distinct moduli all at least 616,000 never cover. The repository also contains the
first formalization this proof builds on: `MinModulus.not_covers` (`MinModulus/Main/Main.lean`), the same statement
for moduli ≥ 16,000, with a simpler evaluation and its own checker.

## The paper

`paper/` holds the paper: `paper/main.pdf` (47 pages) and its LaTeX sources.
- **Build:** `cd paper && tectonic main.tex`, or `latexmk -pdf main.tex`.
- **Figures:** `fig/` holds the figures and `gen/` the generated tables, so the paper builds as is.
- **Figure script:** `make_figures.py` regenerates the figures, but it reads certificate data from the paper's
  accompanying files, which are not in this repository.
- **References to other files:** the paper also refers to other accompanying files, such as the C certificates,
  referee reports and further Lean formalizations. Only the Lean proof of the main theorem is included here.

## Trust base

`lake build MinModulus.Audit` prints:

```
'MinModulus.Checker2Sound.not_covers_14501' depends on axioms: [propext, Classical.choice, Quot.sound,
 MinModulus.Tail2.check2T14501_eq_true._native.native_decide.ax_1_1]
'MinModulus.not_covers' depends on axioms: [propext, Classical.choice, Quot.sound,
 MinModulus.CheckerImpl.check_eq_true._native.native_decide.ax_1_1]
```

Apart from Lean's three standard axioms, each theorem trusts one `native_decide` evaluation.
- The evaluation runs a closed Boolean, a numeric checker written in core Lean, and trusts that it evaluates to
  `true`.
- So it trusts Lean's compiler and runtime, including GMP-backed `Nat` arithmetic.
- The checkers contain no `implemented_by`, `extern`, `unsafe` or `partial` definitions. The only compiler rewrites
  are two `@[csimp]` lemmas in `CheckerImpl/Arith.lean`, which are proved equalities.
- Everything else is checked by the kernel, including the proof that the checker's code computes the quantities it
  claims to (`Checker2Sound/`, `CheckerSound/`).

## Build

```bash
lake exe cache get              # prebuilt Mathlib (v4.34.1)
lake build                      # the main theorem (default target)
lake build MinModulus.Audit     # prints the axioms above
```

Re-running a `native_decide` proof must go through `lake build`: `lake env lean` does not load the precompiled
checker libraries.

A build from scratch takes about 10–15 minutes on a recent machine, plus the Mathlib download. The time is
dominated by `MinModulus.Tail2.check2T14501_eq_true`, the native check of the main theorem: about 10 minutes and
2.6 GB, mostly a sieve of the integers up to 2·10^9. Two further native checks sit in the dependency graph:
- `check2_eq_true`, for moduli ≥ 14,600: about 80 s;
- `check_eq_true`, for moduli ≥ 16,000: about 50 s.

## How the proof works
- **The distortion method.** This is the method of Balister, Bollobás, Morris, Sahasrabudhe and Tiba (`Distortion/`,
  `Arith/`). A covering system gives, at each prime p, a loss. If the losses sum to less than 1, some integer is not
  covered.
- **The comparison theorem** (`Comparison/`). It bounds each loss by an expectation over a random smooth number
  (`Smooth/`). The bound is the hinge E[(U_p(s) − δ_p)^+]/(1 − δ_p), with an explicit tilted law.
- **Per-prime bounds.**
  - The checker `Checker2Impl/` evaluates these expectations exactly for every prime p ≤ 2·10^9, up to explicitly
    bounded truncations. It uses fixed-point arithmetic with directed rounding.
  - The mathematics is in `Checker2Math/`, and the code-level soundness proof is in `Checker2Sound/`. Soundness holds
    for every parameter set satisfying four decidable side conditions.
- **The primes above 2·10^9** (`Tail2/`). An elementary Chebyshev-type bound with constant 0.11882/X for X ≥ 2·10^9
  handles them.
- **The certificate for m = 14,501** is `check2T14501_eq_true`. It gives η = 0.999941815948 and a tail term of
  0.000047341491, so the total is 0.999989157439 < 1.
- **The first formalization** (`CheckerImpl/`, `CheckerMath/`, `CheckerSound/`, `Main/`, `Tail/`) supplies the
  certificate interface `Main.Cert`, the chain `Main.not_covers_of_cert` and the arithmetic, sieve and moment code.
  The main theorem reuses all of these.

| Module | Files | Lines | Contents |
|---|---|---|---|
| `Arith/` | 1 | 679 | Setup: the primes and levels, CRT, the level sets, the hinge step, enlargement |
| `Distortion/` | 1 | 646 | The distortion measures, kernels and tilts; the criterion Σ losses < 1 ⇒ an uncovered point |
| `Comparison/` | 1 | 710 | The comparison theorem (one-coordinate lemma by LP duality, induction over coordinates) |
| `Smooth/` | 8 | 2057 | The tilted law of the smooth number s, U_p(s), moments, hinge bounds, monotone coupling |
| `Tail/` | 1 | 354 | The first formalization's tail bound, 100/(189 X) |
| `Main/` | 3 | 594 | The certificate interface `Cert`, `not_covers_of_cert`, the ≤ 15,999 theorem |
| `CheckerImpl/` | 8 | 1201 | The first checker and `check_eq_true` |
| `CheckerMath/` | 10 | 4011 | Mathematics of the first checker's quantities |
| `CheckerSound/` | 17 | 6130 | Code-level soundness of the first checker |
| `Checker2Impl/` | 6 | 1073 | The second checker (S/B/H decomposition, τ-split, blocks) and `check2_eq_true` |
| `Checker2Math/` | 6 | 2064 | Mathematics of the second checker: identities, joint laws, the pruning bound |
| `Checker2Sound/` | 21 | 6512 | Code-level soundness of the second checker; `run2_sound`; the final theorems |
| `Tail2/` | 12 | 1950 | The sharpened tail, the chain `not_covers_of_certT`, the parameters, `check2T14501_eq_true` |

That is 95 files and about 28,000 lines. `MinModulus.lean` is the root, and `MinModulus/Audit.lean` prints the
axioms.

## Provenance
This repository contains the paper and the part of its Lean development that the main theorem depends on. The
paper's accompanying files also formalize further results: squarefree moduli, odd moduli, and smooth cases. The work
was carried out with substantial assistance from AI systems (Anthropic's Claude), as described in the paper's
acknowledgements.
