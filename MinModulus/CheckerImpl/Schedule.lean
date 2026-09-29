import MinModulus.CheckerImpl.Arith
/-
# `MinModulus.CheckerImpl.Schedule` — parameters and the δ schedule

Status: complete, no `sorry`. Core Lean only.

**δ is an exact rational.** `deltaN P p = dn` means `δ_p = dn / 10^9` (`DDEN = 10^9`), with
`0 ≤ dn ≤ 0.45·10^9` for `p ≤ X := PMAX` (clamped). The certificate's schedule is
`δ₀ p = deltaN P p / 10^9` for `p ≤ X` and `δ₀ p = 1/2` for `p > X` (`deltaCert`).
The tilt is the exact rational `ν_p = 1/(1 − δ_p) = 10^9 / (10^9 − dn)`; the checker never
rounds ν itself, it rounds each derived probability once (see `Moments`, `TauDP`, `Enum`).

For the final parameters: `δ = 0` for `p < 31`, `δ = 1/20` for `31 ≤ p < 50`, knot interpolation
in `log p` for `50 ≤ p < 50000` (values rounded down to multiples of `10^-9`), and
`δ = 4092/10000` for `p ≥ 50000`. **Soundness does not depend on how δ is computed**
(any values in `[0, 1/2]` are valid); `log2Fix` is just a deterministic approximation of `log₂`.
-/
namespace MinModulus.CheckerImpl

/-- `DDEN = 10^9`: denominator of δ-values. -/
def DDEN : Nat := 1000000000

/-- The δ schedule for `p ≥ PD`. Values of δ are in units of `1/10000`. -/
inductive Sched where
  /-- Piecewise linear in `log p` through the points `(ps[i], ds[i]/10000)`,
  constant (`ds[0]`, resp. the last value) outside `[ps[0], ps[last]]`. -/
  | knots (ps : Array Nat) (ds : Array Nat)
  /-- `δ_p = dinf − (dinf − d0)·√(PD/p)` (the C program's smooth schedule with κ = 1/2). -/
  | smoothHalf (d0 dinf : Nat)

/-- All parameters of one run of the checker. -/
structure Params where
  /-- All moduli are `≥ m`. -/
  m : Nat
  /-- The schedule `sched` applies to primes `p ≥ PD`. -/
  PD : Nat
  /-- Primes `PSB ≤ p < PD` get `δ = DSB/10000`; primes `p < min PSB PD` get `δ = 0`. -/
  PSB : Nat
  DSB : Nat
  /-- Comparison (A/B) bound for primes `p ≤ PX`; moment bounds for `PX < p ≤ PMAX`. -/
  PX : Nat
  /-- `X = PMAX`: every prime `≤ X` gets a cost; primes `> X` are the tail. -/
  PMAX : Nat
  /-- Largest prime allowed in the enumerated part `s_A`. -/
  Z0 : Nat
  /-- Enumeration cut-off `X_p = max(10^4, ⌊XC · M^(XE2/2)⌋)`, `M = ⌈m/p⌉`. -/
  XC : Nat
  XE2 : Nat
  /-- Cap on `τ(s_A)` in the τ_A-distribution DP. -/
  KMAX : Nat
  sched : Sched
  /-- For `p > PX`, primes are processed in blocks `[B, B + max 1 (B >>> blockShift))`. -/
  blockShift : Nat

/-- The final configuration (m = 16000, X = 2·10^8): the parameters of `logs/cert16k.txt`. -/
def fullParams : Params where
  m := 16000
  PD := 50
  PSB := 31
  DSB := 500
  PX := 200000
  PMAX := 200000000
  Z0 := 47
  XC := 16
  XE2 := 9
  KMAX := 20000
  sched := .knots #[50, 80, 130, 220, 400, 800, 2000, 8000, 50000]
                  #[700, 1612, 2191, 2679, 3198, 3450, 3762, 4031, 4092]
  blockShift := 13

/-- The development instance: the C program's "fast" configuration
(`rigcert 30000 50 200000 2e7 47 4 3 400000 20000 0 -1 0.1 0.4 0.5`). Not a certificate
(the tail theorem needs `X ≥ 2^27`); used only to compare with the C program. -/
def fastParams : Params where
  m := 30000
  PD := 50
  PSB := 50
  DSB := 0
  PX := 200000
  PMAX := 20000000
  Z0 := 47
  XC := 4
  XE2 := 6
  KMAX := 20000
  sched := .smoothHalf 1000 4000
  blockShift := 13

/-- Deterministic fixed-point approximation of `log₂ x · 2^40` (for `x ≥ 1`), by the
bit-by-bit squaring method with a 60-bit mantissa. -/
def log2Fix (x : Nat) : Nat :=
  let e := Nat.log2 x
  let y := (x <<< 60) >>> e     -- x / 2^e ∈ [1, 2) as a 60-bit fixed-point number
  e * 1099511627776 + go y 0 40
where
  go (y acc : Nat) : Nat → Nat
    | 0 => acc
    | k + 1 =>
      let y2 := (y * y) >>> 60
      if y2 ≥ (2 <<< 60) then go (y2 >>> 1) (2 * acc + 1) k else go y2 (2 * acc) k

/-- `0.45 · 10^9`: every δ (for `p ≤ X`) is clamped to `[0, 0.45]`. -/
def DNMAX : Nat := 450000000

/-- `d · 10^9 / 10000 = d · 10^5` for `d` in units of `1/10000` (exact). -/
def dnOfTenThousandths (d : Nat) : Nat := d * 100000

/-- δ of the knot schedule at `p` (as `dn`, i.e. `δ = dn/10^9`, rounded down). -/
def knotDelta (ps ds : Array Nat) (p : Nat) : Nat :=
  if ps.size = 0 then 0
  else if p ≤ ps[0]! then dnOfTenThousandths ds[0]!
  else if ps[ps.size - 1]! ≤ p then dnOfTenThousandths ds[ds.size - 1]!
  else go 0 ps.size
where
  /-- find the first segment `i` with `p ≤ ps[i+1]` and interpolate in `log p`. -/
  go (i : Nat) : Nat → Nat
    | 0 => dnOfTenThousandths ds[ds.size - 1]!
    | f + 1 =>
      if p ≤ ps[i + 1]! then
        let li := log2Fix ps[i]!
        let li1 := log2Fix ps[i + 1]!
        let lp := log2Fix p
        let w : Int := (li1 : Int) - li
        let num : Int := (ds[i]! : Int) * w + ((ds[i + 1]! : Int) - ds[i]!) * ((lp : Int) - li)
        (num * 100000 / w).toNat
      else go (i + 1) f

/-- δ of the smooth schedule at `p ≥ PD`: `dinf − (dinf − d0)·√(PD/p)` (units `10^-9`). -/
def smoothDelta (PD d0 dinf p : Nat) : Nat :=
  let r := Nat.sqrt (PD * DDEN * DDEN / p)       -- ≈ √(PD/p) · 10^9
  dnOfTenThousandths dinf - cdiv ((dinf - d0) * r) 10000

/-- The δ-value `dn` of a prime `p ≤ X` (`δ_p = dn / 10^9`), clamped to `[0, 0.45]`. -/
def deltaN (P : Params) (p : Nat) : Nat :=
  let raw :=
    if p < P.PD then (if P.PSB ≤ p then dnOfTenThousandths P.DSB else 0)
    else match P.sched with
      | .knots ps ds => knotDelta ps ds p
      | .smoothHalf d0 dinf => smoothDelta P.PD d0 dinf p
  min raw DNMAX

/-- The certificate's schedule as a `(numerator, denominator)` pair: `δ₀ p = num / den`,
`= deltaN P p / 10^9` for `p ≤ X` and `= 1/2` for `p > X`. -/
def deltaCert (P : Params) (p : Nat) : Nat × Nat :=
  if P.PMAX < p then (1, 2) else (deltaN P p, DDEN)

end MinModulus.CheckerImpl
