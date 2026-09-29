import MinModulus.CheckerImpl.Moments
/-
# `MinModulus.Checker2Impl.Params` — parameters and the δ schedule of the second checker

Status: complete, no `sorry`. Core Lean only (no Mathlib). Part of the precompiled Lake library
`Checker2Impl`. Reuses the arithmetic of the first checker (`CheckerImpl.Arith`: P-values
`x / 2^62`, `ONE = 2^62`, `cdiv`, `ratUp`/`ratDn`, `mulUp`/`mulDn` (limb `@[csimp]`), `powUp`), its
δ-value convention (`CheckerImpl.Schedule`: `δ = dn / 10^9`, `DDEN = 10^9`, exact tilt
`ν = 10^9/(10^9 − dn)`, `nuDen dn = 10^9 − dn`) and `log2Fix`.

**δ is an exact rational** `deltaN2 P p / 10^9`, with `deltaN2 P p ≤ 0.45·10^9` (clamp), for `p ≤ X`;
the certificate uses `δ₀ p = 1/2` for `p > X` (`deltaCert2`). Soundness does not depend on how δ is
computed; the knot interpolation only has to be deterministic.

* `p < PD`: `δ = 0` (these primes use the first moment `CheckerImpl.firstMoment`);
* `p ≥ PD`: piecewise linear in `log p` through the knots `(kps[i], kds[i]·10^-6)`, constant outside
  `[kps[0], kps[last]]`, rounded to a multiple of `10^-9` (`log₂` by `log2Fix`).
The blocks `p > PX` need `δ` constant on `(PX, X]`: this holds when `kps[last] ≤ PX`
(`knotDelta6_of_ge`), which `run2` checks at run time (flag `ok`).
-/
namespace MinModulus.Checker2Impl

open MinModulus.CheckerImpl

/-! ## Non-inlined constants (performance only; all are definitionally the originals)

Lean 4.34's code generator inlines a constant whose value is a `Nat` literal `≥ 2^32` (such as
`ONE = 2^62`) at every use and rebuilds it there with `lean_cstr_to_nat` (a decimal-string parse
through GMP) on **every call**. `@[noinline]` keeps such a constant a global that is initialized once.
The hot paths of this checker therefore use `ONE2`, `TWO60`, `ratUp2`, `ratDn2`, `facE1u` instead of
`ONE`, `2^60`, `ratUp`, `ratDn`, `facE1`; each is equal to the original by `rfl`. -/

/-- `ONE = 2^62`, not inlined. -/
@[noinline] def ONE2 : Nat := ONE
theorem ONE2_eq : ONE2 = ONE := rfl

/-- `2^60`, not inlined. -/
@[noinline] def TWO60 : Nat := 1152921504606846976
theorem TWO60_eq : TWO60 = 2 ^ 60 := by decide

/-- `ratUp` with the non-inlined `ONE2`. -/
@[inline] def ratUp2 (num den : Nat) : Nat := cdiv (num * ONE2) den
theorem ratUp2_eq (num den : Nat) : ratUp2 num den = ratUp num den := rfl

/-- `ratDn` with the non-inlined `ONE2`. -/
@[inline] def ratDn2 (num den : Nat) : Nat := num * ONE2 / den
theorem ratDn2_eq (num den : Nat) : ratDn2 num den = ratDn num den := rfl

/-- `facE1` (upper P-value of `E[v+1] = 1 + ν/(q−1)`) with `ratUp2`. -/
def facE1u (q dn : Nat) : Nat := ratUp2 ((q - 1) * nuDen dn + DDEN) ((q - 1) * nuDen dn)
theorem facE1u_eq (q dn : Nat) : facE1u q dn = facE1 q dn := rfl

/-- All parameters of one run of the second checker. -/
structure Params2 where
  /-- All moduli are `≥ m`. -/
  m : Nat
  /-- The tail threshold `X` (every prime `≤ X` gets a cost; the rest is the Lean tail). -/
  X : Nat
  /-- Per-prime evaluation for `p ≤ PX`; blocks for `PX < p ≤ X`. -/
  PX : Nat
  /-- `δ = 0` for `p < PD` (first moment). -/
  PD : Nat
  /-- Knot primes (increasing) and knot δ-values in units of `10^-6`. -/
  kps : Array Nat
  kds : Array Nat
  /-- S/B/H split: `y = N1` when `N1 ≤ YB`, else `y = max ⌈√N1⌉ N2`. -/
  YB : Nat
  /-- The law of `T_H` (and every lower-tail table) lives on `[0, KH]`. -/
  KH : Nat
  /-- The law of `τ_s` (primes `< YS`) lives on `[0, TS]`. -/
  TS : Nat
  /-- The law of `e = Σ_{q ∈ [YS, p)} v_q` lives on `[0, NN]`. -/
  NN : Nat
  /-- DFS pruning threshold: a subtree is pruned when its bound is `< E[τ_S]·E[T] / 2^epsShift`. -/
  epsShift : Nat
  /-- Blocks `[B, B + max 1 (B >>> blockShift))` for `p > PX`. -/
  blockShift : Nat

/-- `0.45·10^9`: every δ (for `p ≤ X`) is clamped to `[0, 0.45]`. -/
def DNMAX2 : Nat := 450000000

/-- δ of the knot schedule at `p` in units of `10^-9` (knot values `ds` in units of `10^-6`),
piecewise linear in `log p`, constant outside the knot range. -/
def knotDelta6 (ps ds : Array Nat) (p : Nat) : Nat :=
  if ps.size = 0 then 0
  else if p ≤ ps[0]! then ds[0]! * 1000
  else if ps[ps.size - 1]! ≤ p then ds[ds.size - 1]! * 1000
  else go 0 ps.size
where
  /-- find the first segment `i` with `p ≤ ps[i+1]` and interpolate in `log p`. -/
  go (i : Nat) : Nat → Nat
    | 0 => ds[ds.size - 1]! * 1000
    | f + 1 =>
      if p ≤ ps[i + 1]! then
        let li := log2Fix ps[i]!
        let li1 := log2Fix ps[i + 1]!
        let lp := log2Fix p
        let w : Int := (li1 : Int) - li
        let num : Int := (ds[i]! : Int) * w + ((ds[i + 1]! : Int) - ds[i]!) * ((lp : Int) - li)
        (num * 1000 / w).toNat
      else go (i + 1) f

/-- Beyond the last knot the schedule is constant. -/
theorem knotDelta6_of_ge {ps ds : Array Nat} {p : Nat} (hs : ps.size ≠ 0)
    (h : ps[ps.size - 1]! ≤ p) (h0 : ¬ p ≤ ps[0]!) :
    knotDelta6 ps ds p = ds[ds.size - 1]! * 1000 := by
  unfold knotDelta6
  simp [hs, h, h0]

/-- The δ-value `dn` of a prime `p ≤ X` (`δ_p = dn / 10^9`), clamped to `[0, 0.45]`. -/
def deltaN2 (P : Params2) (p : Nat) : Nat :=
  if p < P.PD then 0 else min (knotDelta6 P.kps P.kds p) DNMAX2

theorem deltaN2_le (P : Params2) (p : Nat) : deltaN2 P p ≤ DNMAX2 := by
  unfold deltaN2
  split
  · exact Nat.zero_le _
  · exact Nat.min_le_right _ _

/-- The certificate's schedule as a `(numerator, denominator)` pair: `deltaN2 P p / 10^9` for
`p ≤ X`, `1/2` for `p > X` (same convention as `CheckerImpl.deltaCert`). -/
def deltaCert2 (P : Params2) (p : Nat) : Nat × Nat :=
  if P.X < p then (1, 2) else (deltaN2 P p, DDEN)

/-- The knots of the schedule used for the target (the 103-knot schedule of
`certificate-14501/schedule/sched_14501.json` with every knot `≥ 50000` set to `0.42`, i.e.
`r7-method-limit/package_14501/frontier/sched_lean_tail042.json`), δ in units of `10^-6`. -/
def knotPs : Array Nat := #[17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
  97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
  197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
  439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 550, 650, 800, 1000, 1200, 1600, 2000, 2700,
  3500, 5000, 8000, 20000, 50000, 200000]

/-- Knot δ-values in units of `10^-6` (see `knotPs`). -/
def knotDs : Array Nat := #[3750, 5000, 6250, 8750, 36250, 36250, 55000, 73750, 72500, 98150,
  106800, 119050, 123650, 131380, 141290, 155230, 160970, 172510, 178660, 182540, 188650, 198220,
  204200, 206020, 209837, 217630, 223648, 230595, 234931, 236266, 238825, 241289, 242881, 249996,
  259213, 261402, 264497, 266549, 269965, 271361, 267464, 264006, 266240, 268576, 270686, 274956,
  279675, 288000, 296790, 298855, 299341, 301179, 299224, 300443, 299810, 294209, 288986, 288947,
  290166, 292580, 305797, 309213, 314773, 315866, 318408, 319916, 318618, 317664, 316724, 316106,
  315191, 313993, 313793, 315719, 313074, 313538, 310826, 311277, 310119, 311003, 317314, 319036,
  319885, 322807, 323646, 322280, 337726, 352946, 358381, 326000, 348360, 342500, 365220, 363800,
  373440, 382450, 387760, 398100, 404570, 414350, 434850, 420000, 420000]

/-- Parameters for the minimum modulus `m` with the target settings
(`X = 2·10^8`, `PX = 2·10^5`, `PD = 17`, `KH = 4096`, `TS = 2^20`, `NN = 24`, `EPS = 2^-33`,
blocks of relative width `2^-13`). -/
def paramsFor (m : Nat) : Params2 where
  m := m
  X := 200000000
  PX := 200000
  PD := 17
  kps := knotPs
  kds := knotDs
  YB := 23
  KH := 4096
  TS := 1048576
  NN := 24
  epsShift := 33
  blockShift := 13

end MinModulus.Checker2Impl
