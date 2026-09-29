import MinModulus.CheckerImpl.Schedule
/-
# `MinModulus.CheckerImpl.Moments` — first moment, θ-moment factors, `c_θ`, block values

Status: complete, no `sorry`. Core Lean only.

Notation: `q` a prime with δ-value `dn` (`δ_q = dn/10^9`) and exact tilt
`ν = 1/(1 − δ_q) = 10^9/(10^9 − dn)`; `v = v_q` has the tilted law
`P(v = 0) = 1 − ν/q`, `P(v = a) = ν (q−1) q^{−a−1}` (`a ≥ 1`), i.e. `P(v ≥ a) = ν q^{−a}`.
For a cap `γ`, the capped law `min(v, γ)` has `E[f(min(v,γ))] ≤ E[f(v)]` for nondecreasing `f`
(and equality in the limit), so each uncapped moment below also bounds every capped one.
All quantities are upper P-values (numerator over `2^62`) of exact rationals, rounded once.

* `fac2 q dn`  ≥ `E[(v+1)²]      = 1 + ν(3q−1)/(q−1)²`      (exact closed form);
* `fac3 q dn`  ≥ `E[(v+1)³]      = 1 + ν(7q²−2q+1)/(q−1)³`  (exact closed form);
* `fac25 q dn` ≥ `E[(v+1)^{5/2}] = 1 + ν(1−1/q)·Σ_{a≥1} q^{−a}((a+1)^{5/2} − 1)`.
The exact right-hand sides are nonincreasing in `q` for fixed ν (used for blocks `p > PX`).
-/
namespace MinModulus.CheckerImpl

/-- `10^9 − dn`, the denominator of the exact tilt `ν = 10^9/(10^9 − dn)`. -/
@[inline] def nuDen (dn : Nat) : Nat := DDEN - dn

/-- Upper P-value of `1 + ν/(q−1) = E[v+1]`. -/
def facE1 (q dn : Nat) : Nat :=
  ratUp ((q - 1) * nuDen dn + DDEN) ((q - 1) * nuDen dn)

/-- Upper P-value of `E[(v+1)²] = 1 + ν(3q − 1)/(q − 1)²` (`q ≥ 2`). This is also the factor
`tailFactor` of `T = Π (1 + ν_q (3q−1)/(q−1)²)` in the tail criterion. -/
def fac2 (q dn : Nat) : Nat :=
  let d := (q - 1) * (q - 1) * nuDen dn
  ratUp (d + DDEN * (3 * q - 1)) d

/-- Upper P-value of `E[(v+1)³] = 1 + ν(7q² − 2q + 1)/(q − 1)³` (`q ≥ 2`). -/
def fac3 (q dn : Nat) : Nat :=
  let d := (q - 1) * (q - 1) * (q - 1) * nuDen dn
  ratUp (d + DDEN * (7 * q * q - 2 * q + 1)) d

/-- `⌈√n · 2^32⌉ ≥ 2^32·√n`. -/
def sqrt32Up (n : Nat) : Nat := sqrtUp (n * TWO32 * TWO32)

/-- Lower P-value of `Σ_{a=1}^{A} q^{−a} ((a+1)³ − (a+1)² s⁺(a+1))`, where
`s⁺(n) = sqrt32Up n / 2^32 ≥ √n` and `A` is the largest `a` with `q^a ≤ 2^100`; each term is
rounded down and is `≥ 0` since `s⁺(n) ≤ n` for `n ≥ 1`. Loop state: `qa = q^a`. -/
def fac25Sub (q : Nat) (a qa acc : Nat) : Nat → Nat
  | 0 => acc
  | f + 1 =>
    if qa > 1267650600228229401496703205376 then acc   -- 2^100
    else
      let b := a + 1
      let num := b * b * (b * TWO32 - sqrt32Up b)     -- ((a+1)³ − (a+1)² s⁺(a+1)) · 2^32
      fac25Sub q (a + 1) (qa * q) (acc + num * ONE / (TWO32 * qa)) f

/-- Upper P-value of `E[(v+1)^{5/2}]`: `1 + ν (1 − 1/q) · W` with
`W = S₃(q) − Σ_{a ≤ A} q^{−a}((a+1)³ − (a+1)² s⁺(a+1))`,
`S₃(q) = Σ_{a≥1} q^{−a}((a+1)³ − 1) = q(7q² − 2q + 1)/(q − 1)⁴`.
Justification: `(a+1)^{5/2} ≤ (a+1)² s⁺(a+1)` for `a ≤ A`, `(a+1)^{5/2} ≤ (a+1)³` for `a > A`,
so `Σ_{a≥1} q^{−a}((a+1)^{5/2} − 1) ≤ W`. -/
def fac25 (q dn : Nat) : Nat :=
  let q1 := q - 1
  let s3 := cdiv (q * (7 * q * q - 2 * q + 1) * ONE) (q1 * q1 * q1 * q1)
  let W := s3 - fac25Sub q 1 q 0 128
  ONE + cdiv (DDEN * q1 * W) (nuDen dn * q)

/-- Upper P-value of `c_2(δ) = 1/(4δ)` for `δ = dn/10^9 > 0`. -/
def cTheta2 (dn : Nat) : Nat := ratUp DDEN (4 * dn)

/-- Upper P-value of `c_3(δ) = 4/(27δ²)`. -/
def cTheta3 (dn : Nat) : Nat := ratUp (4 * DDEN * DDEN) (27 * dn * dn)

/-- Upper P-value of `c_{5/2}(δ) = (6/(25δ))·√(3/(5δ))`. -/
def cTheta25 (dn : Nat) : Nat :=
  mulUp (ratUp (6 * DDEN) (25 * dn)) (sqrtRatUp (3 * DDEN) (5 * dn))

/-- **Moment bound, per prime of a block.** For every prime `p ≥ B` of a block whose primes all
use `δ = dn/10^9 > 0`, given upper P-values `ET2, ET25, ET3` of `E[τ(s)^θ]` (`s` over the primes
below `p`) valid for all `p` in the block: upper P-value of
`min_θ c_θ(δ) · ET_θ / ((B − 1)^θ (1 − δ))`, θ ∈ {2, 5/2, 3}.
Here `c_θ(δ) = (δ/(θ−1))(θδ/(θ−1))^{−θ} = max_{u ≥ δ} (u − δ)/u^θ`, so
`max(0, u − δ) ≤ c_θ(δ)·u^θ` for all `u ≥ 0`, and `U_p(s) ≤ τ(s)/(p−1)`.
Uses `(B−1)^{5/2} ≥ (B−1)² · ⌊√(B−1)·2^32⌋ / 2^32`. -/
def blockVal (B dn ET2 ET25 ET3 : Nat) : Nat :=
  let nd := nuDen dn
  let pm := B - 1
  let k2 := cdiv (cTheta2 dn * ET2 * DDEN) (pm * pm * nd * ONE)
  let k3 := cdiv (cTheta3 dn * ET3 * DDEN) (pm * pm * pm * nd * ONE)
  let sq := Nat.sqrt (pm * TWO32 * TWO32)
  let k25 := cdiv (cTheta25 dn * ET25 * DDEN * TWO32) (pm * pm * sq * nd * ONE)
  min k2 (min k25 k3)

/-- `true` iff every prime factor of `n ≥ 1` lies in `ps` (strip all factors of each `q ∈ ps`). -/
def isSmoothOver (ps : Array Nat) (n : Nat) : Bool := go 0 n ps.size
where
  strip (q x : Nat) : Nat → Nat
    | 0 => x
    | f + 1 => if x % q == 0 then strip q (x / q) f else x
  go (i x : Nat) : Nat → Bool
    | 0 => x == 1
    | f + 1 => go (i + 1) (strip ps[i]! x 64) f

/-- `J(n) = #{j ≥ 1 : n < ⌈m/p^j⌉}` for `n ≥ 1` (loop state `pj = p^j`). -/
def numThresholdsAbove (m p n : Nat) : Nat := go p 0 64
where
  go (pj acc : Nat) : Nat → Nat
    | 0 => acc
    | f + 1 => if n < cdiv m pj then go (pj * p) (acc + 1) f else acc

/-- **First-moment bound** at a prime `p` (with `δ_p = 0`) all of whose smaller primes `ps` have
`δ = 0` (tilt 1). Upper P-value of
`E[U_p(s)] = T1/(p−1) − Σ_{1 ≤ n < ⌈m/p⌉, n ps-smooth} c(n)/n`, with `T1 = Π_{q∈ps} q/(q−1)`,
`c(n) = Σ_{j≥1, n < ⌈m/p^j⌉} p^{−j} = (p^{J(n)} − 1)/((p−1) p^{J(n)})`, `J = numThresholdsAbove`.
(Derivation: `w_p(d) = 1/(p−1) − c(d)`, `P(d | s) = 1/d`, `Σ_{d ps-smooth} 1/d = T1`; for a cap
the sum runs over fewer `d`, all terms `w_p(d)/d ≥ 0`, so the uncapped value is an upper bound.) -/
def firstMoment (m p : Nat) (ps : Array Nat) : Nat :=
  let numT := ps.foldl (fun a q => a * q) 1
  let denT := ps.foldl (fun a q => a * (q - 1)) 1
  let t1 := cdiv (numT * ONE) (denT * (p - 1))
  t1 - go 1 (cdiv m p - 1) 0
where
  go (n : Nat) : Nat → Nat → Nat
    | 0, acc => acc
    | f + 1, acc =>
      if isSmoothOver ps n then
        let pJ := p ^ numThresholdsAbove m p n
        go (n + 1) f (acc + (pJ - 1) * ONE / ((p - 1) * pJ * n))
      else go (n + 1) f acc

end MinModulus.CheckerImpl
