import MinModulus.Checker2Impl.Params
/-
# `MinModulus.Checker2Impl.Laws` — point masses, DP steps, lost mass, prefix/suffix tables

Status: complete, no `sorry`. Core Lean only.

Notation: `q ≥ 2` with δ-value `dn` (`δ_q = dn/10^9`, `dn < 10^9`), exact tilt
`ν = 10^9/nd`, `nd = nuDen dn = 10^9 − dn`. The exponent `v = v_q` has the tilted law
`P(v = 0) = 1 − ν/q`, `P(v = a) = ν (q−1) q^{−a−1}` (`a ≥ 1`), i.e. `P(v ≥ a) = ν q^{−a}`
(`Smooth.rho`; for a cap `γ` these point masses are exact for `a < γ`, `TauLaw.rho_eq_pointMass`).
All values are **upper** P-values (numerators over `2^62`) unless stated otherwise.

* `pmArr q dn A` : `pm[a] ≥ 2^62·P(v = a)` for `a ≤ A` (one division for `a ≤ 1`, then
  `pm[a+1] = ⌈pm[a]/q⌉`, valid since `P(v = a+1) = P(v = a)/q` for `a ≥ 1`);
* `hUp q dn A`   : `≥ 2^62·E[(v+1)·1{v ≥ A}]`; `= facE1` for `A = 0`, and
  `ν q^{−A} (A + 1 + 1/(q−1)) = 10^9((A+1)(q−1)+1)/(nd q^A (q−1))` for `A ≥ 1`
  (`CheckerMath.expect1_hA_le`, every cap);
* `e2Up q dn`    : `≥ 2^62·E[2^v] = 2^62·(1 + ν/(q−2))` (`q ≥ 3`);
* `h2Up q dn A`  : `≥ 2^62·E[2^v·1{v ≥ A}] = 2^62·ν (q−1) 2^A / (q^A (q−2))` (`q ≥ 3`);
* `acut60 q`     : the largest `a ≤ 64` with `q^a ≤ 2^60` (exponent cut of the τ_s and e laws).

## DP primitive (the only one)
`dpRange Dn D K pm alo ahi` adds, for every `1 ≤ t ≤ K` with `D[t] ≠ 0` and every
`a ∈ [alo, ahi)` with `t·(a+1) ≤ K`, the value `mulUp D[t] pm[a]` to `Dn[t·(a+1)]`.
(`Dn` must have size `> K`; nothing else is read or written.) All laws of the checker are
iterates of it:
* full law step (no exponent cut, lower-tail tables): `dpRange (zeros (K+1)) D K pm 0 K`;
* τ_s step with exponent cut `ac`, on the **weighted** law `W[T] ≥ T·P(τ_s = T, kept)`:
  `dpRange (zeros (TS+1)) W TS (weightByTau pm) 0 (ac+1)` — the dropped pairs are exactly
  `t(a+1) > TS ∨ a > ac`, i.e. `a ≥ min(⌊TS/t⌋, ac+1) = TauLaw.lostThr TS ac t`. (Weighted masses:
  with round-up fixed point a negligible mass sits at `≥ 1` ulp; unweighted, it would then be
  amplified by the weight `T ≤ TS` of the hinge sums. Weighted, the ulp is never amplified.)
* the (T, b) rows of the S/B/H bound (`Rows.step`).

## Tables
* `prefixTables D` : `(S0, S1)` with `S0[k] = Σ_{j ≤ k} D[j]`, `S1[k] = Σ_{j ≤ k} j·D[j]` (exact);
* `suffixTablesW W TS` : `(SW, SV)` of a weighted law, `SW[k] = Σ_{T ≥ k} W[T]`,
  `SV[k] = Σ_{T ≥ k} ⌊W[T]·2^20/T⌋`.
-/
namespace MinModulus.Checker2Impl

open MinModulus.CheckerImpl

/-- Upper P-values of `P(v = a)`, `a = 0 … A` (see the module docstring). -/
def pmArr (q dn A : Nat) : Array Nat :=
  let nd := nuDen dn
  let p0 := ratUp2 (q * nd - DDEN) (q * nd)
  if A = 0 then #[p0]
  else
    let p1 := ratUp2 (DDEN * (q - 1)) (nd * q * q)
    go q (A - 1) p1 #[p0, p1]
where
  /-- appends `⌈x/q⌉, ⌈x/q²⌉, …` (`fuel` entries); `x` is the last entry. -/
  go (q : Nat) : Nat → Nat → Array Nat → Array Nat
    | 0, _, acc => acc
    | f + 1, x, acc => go q f (cdiv x q) (acc.push (cdiv x q))

/-- Upper P-value of `h(A) = E[(v+1)·1{v ≥ A}]` (`A = 0`: `E[v+1] = 1 + ν/(q−1)`). -/
def hUp (q dn A : Nat) : Nat :=
  if A = 0 then facE1u q dn
  else ratUp2 (DDEN * ((A + 1) * (q - 1) + 1)) (nuDen dn * q ^ A * (q - 1))

/-- `#[hUp q dn 0, …, hUp q dn A]`. -/
def hArr (q dn A : Nat) : Array Nat := go 0 (A + 1) (Array.emptyWithCapacity (A + 1))
where
  go (a : Nat) : Nat → Array Nat → Array Nat
    | 0, acc => acc
    | f + 1, acc => go (a + 1) f (acc.push (hUp q dn a))

/-- Upper P-value of `E[2^v] = 1 + ν/(q−2)` (`q ≥ 3`). -/
def e2Up (q dn : Nat) : Nat :=
  ratUp2 ((q - 2) * nuDen dn + DDEN) ((q - 2) * nuDen dn)

/-- Upper P-value of `E[2^v·1{v ≥ A}] = ν (q−1) 2^A / (q^A (q−2))` (`q ≥ 3`). -/
def h2Up (q dn A : Nat) : Nat :=
  ratUp2 (DDEN * (q - 1) * 2 ^ A) (nuDen dn * q ^ A * (q - 2))

/-- The largest `a ≤ 64` with `q^a ≤ 2^60` (for `q ≥ 2`). -/
def acut60 (q : Nat) : Nat := go 0 1 64
where
  go (a qa : Nat) : Nat → Nat
    | 0 => a
    | f + 1 => if qa * q ≤ TWO60 then go (a + 1) (qa * q) f else a

/-- An array of `n` zeros. -/
@[inline] def zeros (n : Nat) : Array Nat := Array.replicate n 0

/-- **The DP primitive.** For every `1 ≤ t ≤ K` with `D[t] ≠ 0` and every `a ∈ [alo, ahi)` with
`t·(a+1) ≤ K`: `Dn[t·(a+1)] += mulUp D[t] pm[a]`. -/
def dpRange (Dn D : Array Nat) (K : Nat) (pm : Array Nat) (alo ahi : Nat) : Array Nat :=
  outer 1 K Dn
where
  inner (d t a : Nat) : Nat → Array Nat → Array Nat
    | 0, Dn => Dn
    | f + 1, Dn =>
      let T := t * (a + 1)
      if T ≤ K then inner d t (a + 1) f (Dn.set! T (Dn[T]! + mulUp d pm[a]!)) else Dn
  outer (t : Nat) : Nat → Array Nat → Array Nat
    | 0, Dn => Dn
    | f + 1, Dn =>
      let d := D[t]!
      outer (t + 1) f (if d == 0 then Dn else inner d t alo (ahi - alo) Dn)

/-- Full law step on `[0, K]` (no exponent cut): the law of `T·(v+1)` restricted to `T·(v+1) ≤ K`.
Needs `pm.size ≥ K` (entries `a ≤ K − 1`). -/
@[inline] def lawStepFull (D : Array Nat) (K : Nat) (pm : Array Nat) : Array Nat :=
  dpRange (zeros (K + 1)) D K pm 0 K

/-- Lost-mass increment of one τ-step on a **weighted** law `W[t] ≥ 2^62·t·P(τ = t, kept)`, with
table bound `TM` and exponent cut `ac`: `Σ_{1 ≤ t ≤ TM, W[t] ≠ 0} mulUp W[t] hA[min (TM/t) (ac+1)]`
(`hA = hArr q dn (ac+1)`; `TauLaw.lostMass_insert`: the paths leaving the table at this step are the
exponents `a ≥ min(⌊TM/t⌋, ac+1)`, contributing `P(τ = t)·t·E[(v+1)1{v ≥ A}]`, and
`E[(v+1)1{v ≥ A}] ≤ hA[A]`). -/
def lostSumW (W : Array Nat) (TM ac : Nat) (hA : Array Nat) : Nat := go 1 TM 0
where
  go (t : Nat) : Nat → Nat → Nat
    | 0, acc => acc
    | f + 1, acc =>
      let w := W[t]!
      if w == 0 then go (t + 1) f acc
      else go (t + 1) f (acc + mulUp w hA[min (TM / t) (ac + 1)]!)

/-- `#[1·pm[0], 2·pm[1], …]`: the multipliers of the weighted τ-step (`(a+1)·P(v = a)`, upper). -/
def weightByTau (pm : Array Nat) : Array Nat := go 0 pm.size (Array.emptyWithCapacity pm.size)
where
  go (a : Nat) : Nat → Array Nat → Array Nat
    | 0, acc => acc
    | f + 1, acc => go (a + 1) f (acc.push ((a + 1) * pm[a]!))

/-- `#[pm[0], 2·pm[1], 4·pm[2], …]`: the multipliers of the weighted e-step (`2^a·P(v = a)`). -/
def weightByPow2 (pm : Array Nat) : Array Nat := go 0 pm.size (Array.emptyWithCapacity pm.size)
where
  go (a : Nat) : Nat → Array Nat → Array Nat
    | 0, acc => acc
    | f + 1, acc => go (a + 1) f (acc.push (pm[a]! <<< a))

/-- Prefix tables `(S0, S1)` of `D` (same size): `S0[k] = Σ_{j ≤ k} D[j]`, `S1[k] = Σ_{j ≤ k} j·D[j]`. -/
def prefixTables (D : Array Nat) : Array Nat × Array Nat :=
  go 0 0 0 (Array.emptyWithCapacity D.size) (Array.emptyWithCapacity D.size) D.size
where
  go (j s0 s1 : Nat) (S0 S1 : Array Nat) : Nat → Array Nat × Array Nat
    | 0 => (S0, S1)
    | f + 1 =>
      let s0' := s0 + D[j]!
      let s1' := s1 + j * D[j]!
      go (j + 1) s0' s1' (S0.push s0') (S1.push s1') f

/-- Suffix tables of a **weighted** law `W[T] ≥ 2^62·T·P(τ = T, kept)` on `[0, TS]` (size `TS + 2`,
zero at `0` and `TS + 1`): `SW[k] = Σ_{k ≤ T ≤ TS} W[T]` and
`SV[k] = Σ_{k ≤ T ≤ TS} ⌊W[T]·2^20/T⌋` (a lower bound of `2^20·Σ_{T ≥ k} W[T]/T`). For
`y ∈ [k − 1, k)`, `Σ_{T ≥ k} (T − y)·P(T) ≤ Σ_{T ≥ k} (1 − y/T)·W[T]/2^62 ≤ (SW[k] − y·SV[k]/2^20)/2^62`. -/
def suffixTablesW (W : Array Nat) (TS : Nat) : Array Nat × Array Nat :=
  go TS 0 0 (zeros (TS + 2)) (zeros (TS + 2)) TS
where
  go (T aw av : Nat) (SW SV : Array Nat) : Nat → Array Nat × Array Nat
    | 0 => (SW, SV)
    | f + 1 =>
      let aw' := aw + W[T]!
      let av' := av + (W[T]! <<< 20) / T
      go (T - 1) aw' av' (SW.set! T aw') (SV.set! T av') f

end MinModulus.Checker2Impl
