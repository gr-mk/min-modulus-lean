/-
# `MinModulus.CheckerImpl.Arith` — exact natural-number arithmetic with explicit rounding

Status: complete, no `sorry`. Core Lean only (no Mathlib).

## Number conventions used by the whole checker

* **P-values.** A natural number `x` that stands for a real number means `x / 2^62`
  (`ONE = 2^62` is the real number 1). Probabilities, expectations, costs and running
  products are P-values. Naturals below `2^63` are unboxed machine words at run time,
  so the hot loops (the τ-DP and the enumeration) only handle P-values `< 2`; larger
  P-values are ordinary big naturals (always correct, merely slower).
* **δ-values.** A distortion `δ` is stored as `dn : Nat`, meaning exactly `dn / 2^32`.
* Every function that rounds states the direction in its docstring. Upper bounds are
  obtained with `cdiv`/`mulUp`/`ratUp`, lower bounds with `/`/`mulDn`/`ratDn`.
* `Nat` subtraction `a - b` is truncated at `0`; whenever it is used for an *upper* bound
  of a real difference `A - B` we have `a ≥ A` and `b ≤ B`, and then `a - b ≥ A - B`.

The only non-obvious implementations are `mulUp`/`mulDn`, which split their arguments
into 31-bit limbs so that no intermediate product leaves the machine-word range when
both arguments are `≤ 2^62`. They are *proved* equal to their one-line specifications
and installed with `@[csimp]`, so every proof can use the specification.
-/
namespace MinModulus.CheckerImpl

/-- `ONE = 2^62`: the P-value of the real number `1`. -/
def ONE : Nat := 4611686018427387904
/-- `M31 = 2^31 - 1` (limb mask). -/
def M31 : Nat := 2147483647
/-- `TWO32 = 2^32`: denominator of δ-values. -/
def TWO32 : Nat := 4294967296

theorem ONE_eq : ONE = 2 ^ 62 := by decide
theorem M31_eq : M31 = 2 ^ 31 - 1 := by decide
theorem TWO32_eq : TWO32 = 2 ^ 32 := by decide

/-- Ceiling division. For `b > 0`: `cdiv a b = ⌈a / b⌉`, i.e. `a ≤ b * cdiv a b < a + b`. -/
@[inline] def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Upper P-value of the rational `num / den` (`den > 0`): `⌈num · 2^62 / den⌉`. -/
@[inline] def ratUp (num den : Nat) : Nat := cdiv (num * ONE) den

/-- Lower P-value of the rational `num / den` (`den > 0`): `⌊num · 2^62 / den⌋`. -/
@[inline] def ratDn (num den : Nat) : Nat := num * ONE / den

/-- Product of two P-values, rounded up: `mulUp x y = ⌈x · y / 2^62⌉`. -/
def mulUp (x y : Nat) : Nat := (x * y + (ONE - 1)) / ONE

/-- Product of two P-values, rounded down: `mulDn x y = ⌊x · y / 2^62⌋`. -/
def mulDn (x y : Nat) : Nat := x * y / ONE

/-- Limb implementation of `mulUp` (machine-word arithmetic when `x, y ≤ 2^62`). -/
def mulUpImpl (x y : Nat) : Nat :=
  let x1 := x >>> 31
  let x0 := x &&& M31
  let y1 := y >>> 31
  let y0 := y &&& M31
  x1 * y1 + ((x1 * y0 + x0 * y1 + ((x0 * y0 + M31) >>> 31) + M31) >>> 31)

/-- Limb implementation of `mulDn`. -/
def mulDnImpl (x y : Nat) : Nat :=
  let x1 := x >>> 31
  let x0 := x &&& M31
  let y1 := y >>> 31
  let y0 := y &&& M31
  x1 * y1 + ((x1 * y0 + x0 * y1 + ((x0 * y0) >>> 31)) >>> 31)

theorem mulUp_eq_mulUpImpl (x y : Nat) : mulUp x y = mulUpImpl x y := by
  unfold mulUp mulUpImpl
  simp only [Nat.shiftRight_eq_div_pow, M31_eq, Nat.and_two_pow_sub_one_eq_mod, ONE_eq]
  have hx := Nat.div_add_mod x (2^31)
  have hy := Nat.div_add_mod y (2^31)
  generalize x / 2^31 = x1 at hx ⊢
  generalize x % 2^31 = x0 at hx ⊢
  generalize y / 2^31 = y1 at hy ⊢
  generalize y % 2^31 = y0 at hy ⊢
  subst hx hy
  have e : (2 ^ 31 * x1 + x0) * (2 ^ 31 * y1 + y0) + (2 ^ 62 - 1)
      = ((x0 * y0 + (2^31 - 1)) + (x1 * y0 + x0 * y1 + (2^31 - 1)) * 2^31) + (x1 * y1) * 2^62 := by
    grind
  rw [e, Nat.add_mul_div_right _ _ (by decide : 0 < 2^62)]
  have h62 : (2:Nat)^62 = 2^31 * 2^31 := by decide
  rw [h62, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by decide : 0 < 2^31)]
  grind

theorem mulDn_eq_mulDnImpl (x y : Nat) : mulDn x y = mulDnImpl x y := by
  unfold mulDn mulDnImpl
  simp only [Nat.shiftRight_eq_div_pow, M31_eq, Nat.and_two_pow_sub_one_eq_mod, ONE_eq]
  have hx := Nat.div_add_mod x (2^31)
  have hy := Nat.div_add_mod y (2^31)
  generalize x / 2^31 = x1 at hx ⊢
  generalize x % 2^31 = x0 at hx ⊢
  generalize y / 2^31 = y1 at hy ⊢
  generalize y % 2^31 = y0 at hy ⊢
  subst hx hy
  have e : (2 ^ 31 * x1 + x0) * (2 ^ 31 * y1 + y0)
      = (x0 * y0 + (x1 * y0 + x0 * y1) * 2^31) + (x1 * y1) * 2^62 := by
    grind
  rw [e, Nat.add_mul_div_right _ _ (by decide : 0 < 2^62)]
  have h62 : (2:Nat)^62 = 2^31 * 2^31 := by decide
  rw [h62, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by decide : 0 < 2^31)]
  grind

/-- The compiled code uses the limb implementation; proofs use `mulUp`'s definition. -/
@[csimp] theorem mulUp_csimp : @mulUp = @mulUpImpl := by
  funext x y; exact mulUp_eq_mulUpImpl x y

@[csimp] theorem mulDn_csimp : @mulDn = @mulDnImpl := by
  funext x y; exact mulDn_eq_mulDnImpl x y

/-! ### Specifications of the rounding primitives (proved) -/

/-- `cdiv` rounds up. -/
theorem cdiv_spec {a b : Nat} (hb : 0 < b) : a ≤ cdiv a b * b := by
  unfold cdiv
  have h := Nat.lt_mul_div_succ (a + b - 1) hb
  rw [Nat.mul_succ, Nat.mul_comm] at h
  omega

/-- `cdiv` is the least such multiple. -/
theorem cdiv_lt {a b : Nat} (hb : 0 < b) : cdiv a b * b < a + b := by
  unfold cdiv
  have h := Nat.div_mul_le_self (a + b - 1) b
  omega

/-- `mulUp` rounds up: `x·y/2^62 ≤ mulUp x y / 1`. -/
theorem mulUp_spec (x y : Nat) : x * y ≤ mulUp x y * ONE := by
  have h : mulUp x y = cdiv (x * y) ONE := by
    unfold mulUp cdiv
    rw [Nat.add_sub_assoc (by decide : 1 ≤ ONE)]
  rw [h]; exact cdiv_spec (by decide)

/-- `mulDn` rounds down. -/
theorem mulDn_spec (x y : Nat) : mulDn x y * ONE ≤ x * y := Nat.div_mul_le_self _ _

/-- `ratUp num den / 2^62 ≥ num/den`. -/
theorem ratUp_spec {num den : Nat} (h : 0 < den) : num * ONE ≤ ratUp num den * den :=
  cdiv_spec h

/-- `ratDn num den / 2^62 ≤ num/den`. -/
theorem ratDn_spec (num den : Nat) : ratDn num den * den ≤ num * ONE := Nat.div_mul_le_self _ _

/-- Binary exponentiation of P-values with every product rounded up.
Invariant: `(acc/2^62) · (b/2^62)^e ≥` the real power being computed. -/
def powUpAux (b e acc : Nat) : Nat :=
  if h : e = 0 then acc
  else powUpAux (mulUp b b) (e / 2) (if e % 2 = 1 then mulUp acc b else acc)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Upper P-value of `(x / 2^62)^n`. -/
def powUp (x n : Nat) : Nat := powUpAux x n ONE

/-- `⌈√n⌉`. -/
def sqrtUp (n : Nat) : Nat :=
  let s := Nat.sqrt n
  if s * s = n then s else s + 1

/-- Upper P-value of `√(a / b)` (for `b > 0`): `⌈√⌈a · 2^124 / b⌉⌉ ≥ 2^62 · √(a/b)`. -/
def sqrtRatUp (a b : Nat) : Nat := sqrtUp (cdiv (a * ONE * ONE) b)

/-- `a[i] += v`, growing the array with zeros if `i` is out of range. -/
@[inline] def growAdd (a : Array Nat) (i v : Nat) : Array Nat :=
  if i < a.size then a.set! i (a[i]! + v)
  else
    let a' := a ++ Array.replicate (i + 1 - a.size) 0
    a'.set! i v

/-- Read with default `0` out of range. -/
@[inline] def getD0 (a : Array Nat) (i : Nat) : Nat := a.getD i 0

end MinModulus.CheckerImpl
