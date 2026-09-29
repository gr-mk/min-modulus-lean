import MinModulus.CheckerImpl.Moments
/-
# `MinModulus.CheckerImpl.TauDP` — laws of τ(s_A), τ(s_B), and the functions FB and G

Status: complete, no `sorry`. Core Lean only.

Notation. For a finite set `Q` of primes with tilts `ν_q`, `τ = τ(Π_{q∈Q} q^{v_q}) = Π_{q∈Q} (v_q + 1)`
with independent tilted exponents `v_q` (law in `Moments.lean`). A DP over `Q` processes the
primes one by one; a *path* (exponent vector) is **kept** if every exponent satisfies
`v_q ≤ acut_q` and every partial product of the factors `v_q + 1` stays below the size bound
`N` of the array; otherwise it is **lost**.

* `dpStep` (one prime) and its iterates compute, entrywise, upper (`mulUp`, `law.up`) or lower
  (`mulDn`, `law.dn`) bounds of `P(τ = T, path kept)`, `1 ≤ T < N`. Zero entries are skipped:
  they contribute nothing (this is what makes the dense arrays cheap, since after exponent
  truncation the support consists of smooth numbers).
* **B part** (`BState`): only `T < N` is needed, because of the exact identity
  `E[(τ − c)^+] = E[τ] − c + E[(c − τ)^+]` and, for `c < N`,
  `E[(c − τ)^+] ≤ Σ_{T ≤ ⌊c⌋} (c − T)·P(τ = T, kept) + c·P(some v_q > acut_q)`
  (a path lost by exceeding `N` has final `τ ≥ N > c`, so it contributes `0`).
  Hence `fbUp` bounds `FB(c) = E[(τ_B − c)^+]` with no truncation of the τ-range.
* **A part** (`AState`): arrays of size `KMAX + 1`, both directions, and
  `tailA = E[τ_A] − Σ_k k·(lower bound of P(τ_A = k, kept)) ≥ E[τ_A ; lost]`.
-/
namespace MinModulus.CheckerImpl

/-- Truncated exponent law of one prime. For `a ≤ acut`: `up[a] ≥ 2^62·P(v = a) ≥ dn[a]`;
`lostUp ≥ 2^62·P(v > acut) = 2^62·ν q^{−(acut+1)}`. -/
structure ExpLaw where
  acut : Nat
  up : Array Nat
  dn : Array Nat
  lostUp : Nat

/-- Builds the law of `v_q` for the δ-value `dn` (exact tilt `ν = 10^9/(10^9 − dn)`), with `acut`
the largest `a ≤ 64` such that `q^a ≤ 2^bits`. With `nd = 10^9 − dn`:
`P(v = 0) = (q·nd − 10^9)/(q·nd)`, `P(v = a) = 10^9 (q−1)/(nd · q^(a+1))`,
`P(v > acut) = 10^9/(nd · q^(acut+1))`; `up`/`dn`/`lostUp` are these rounded up/down/up. -/
def mkExpLaw (q dn bits : Nat) : ExpLaw :=
  let nd := nuDen dn
  let lim := 1 <<< bits
  let p0 := q * nd - DDEN
  go nd lim 1 q #[ratUp p0 (q * nd)] #[ratDn p0 (q * nd)] 64
where
  /-- state: `qa = q^a`; the arrays hold the entries `0 … a−1`. -/
  go (nd lim a qa : Nat) (up dn : Array Nat) : Nat → ExpLaw
    | 0 => ⟨a - 1, up, dn, ratUp DDEN (nd * qa)⟩
    | f + 1 =>
      if qa ≤ lim then
        let qa1 := qa * q
        go nd lim (a + 1) qa1 (up.push (ratUp (DDEN * (q - 1)) (nd * qa1)))
          (dn.push (ratDn (DDEN * (q - 1)) (nd * qa1))) f
      else ⟨a - 1, up, dn, ratUp DDEN (nd * qa)⟩

/-- Product of P-values rounded up (`up = true`, `mulUp`) or down (`up = false`, `mulDn`). -/
@[inline] def mulR (up : Bool) (x y : Nat) : Nat := if up then mulUp x y else mulDn x y

/-- One DP step for one prime with truncated law `law[0..acut]`:
`dpStep up D N law acut = Dn` where, for `1 ≤ T < N`,
`Dn[T] = Σ_{t ≥ 1, a ≤ acut, t·(a+1) = T, D[t] ≠ 0} mulR up D[t] law[a]`
(`D` and `Dn` have size `N`; pairs with `t·(a+1) ≥ N` are dropped; `Dn[0] = 0`). -/
def dpStep (up : Bool) (D : Array Nat) (N : Nat) (law : Array Nat) (acut : Nat) : Array Nat :=
  outer 1 (N - 1) (Array.replicate N 0)
where
  inner (d t a : Nat) : Nat → Array Nat → Array Nat
    | 0, Dn => Dn
    | f + 1, Dn =>
      let T := t * (a + 1)
      if T < N then inner d t (a + 1) f (Dn.set! T (Dn[T]! + mulR up d law[a]!)) else Dn
  outer (t : Nat) : Nat → Array Nat → Array Nat
    | 0, Dn => Dn
    | f + 1, Dn =>
      let d := D[t]!
      outer (t + 1) f (if d == 0 then Dn else inner d t 0 (acut + 1) Dn)

/-- State of the B-part DP (primes `q ∈ B`, processed in any order).
* `D[T] ≥ 2^62·P(τ_B = T, kept)` for `1 ≤ T < D.size` (upper bounds);
* `EB ≥ 2^62·E[τ_B] = 2^62·Π_{q∈B} (1 + ν_q/(q−1))`;
* `lost ≥ 2^62·P(∃ q ∈ B, v_q > acut_q)` (union bound). -/
structure BState where
  D : Array Nat
  EB : Nat
  lost : Nat

/-- Empty B part: `τ_B = 1` surely. -/
def BState.init (N : Nat) : BState := ⟨(Array.replicate N 0).set! 1 ONE, ONE, 0⟩

/-- Adds prime `q` (δ-value `dn`) to the B part; exponents with `q^a > 2^60` are truncated. -/
def BState.addPrime (st : BState) (q dn : Nat) : BState :=
  let law := mkExpLaw q dn 60
  { D := dpStep true st.D st.D.size law.up law.acut
    EB := mulUp st.EB (facE1 q dn)
    lost := st.lost + law.lostUp }

/-- State of the A part (primes `q ≤ z`), arrays indexed by `k ≤ KMAX`.
* `up[k] ≥ 2^62·P(τ_A = k, kept) ≥ dn[k]`;
* `EA ≥ 2^62·E[τ_A]`;
* `tailA ≥ 2^62·E[τ_A ; lost]`, via `E[τ_A;lost] = E[τ_A] − Σ_k k·P(τ_A = k, kept)`;
* `kTop`: every `k > kTop` has `up[k] = 0`.
Exponents are truncated at `q^a > 2^62`, so every `s_A ≤ 2^62` with `τ(s_A) ≤ KMAX` is kept. -/
structure AState where
  up : Array Nat
  dn : Array Nat
  EA : Nat
  tailA : Nat
  kTop : Nat

/-- Builds the A part for the primes `aps` with δ-values `adns`. -/
def buildA (aps adns : Array Nat) (KMAX : Nat) : AState :=
  let init := (Array.replicate (KMAX + 1) 0).set! 1 ONE
  let (up, dn, EA) := go 0 init init ONE aps.size
  let sumKdn := sumK dn 1 0 KMAX
  let kTop := top up KMAX KMAX
  ⟨up, dn, EA, EA - sumKdn, kTop⟩
where
  go (i : Nat) (up dn : Array Nat) (EA : Nat) : Nat → Array Nat × Array Nat × Nat
    | 0 => (up, dn, EA)
    | f + 1 =>
      let q := aps[i]!
      let d := adns[i]!
      let law := mkExpLaw q d 62
      go (i + 1) (dpStep true up (KMAX + 1) law.up law.acut)
        (dpStep false dn (KMAX + 1) law.dn law.acut) (mulUp EA (facE1 q d)) f
  /-- `Σ_{j=k}^{k+fuel−1} j·dn[j]` (called with `k = 1`, `fuel = KMAX`). -/
  sumK (dn : Array Nat) (k acc : Nat) : Nat → Nat
    | 0 => acc
    | f + 1 => sumK dn (k + 1) (acc + k * dn[k]!) f
  /-- largest `k ≤ start` with `up[k] ≠ 0` (or 0). -/
  top (up : Array Nat) (k : Nat) : Nat → Nat
    | 0 => k
    | f + 1 => if up[k]! == 0 then top up (k - 1) f else k

/-- Prefix tables of the B distribution for `j = 0 … K`:
`S0[j] = Σ_{T ≤ j} D[T]` (P-values, exact) and `PP[j] = Σ_{i < j} ⌈S0[i]/2^20⌉`
(scale `2^42`, rounded up), so that `2^20·PP[j] ≥ Σ_{T ≤ j} (j − T)·D[T]`. -/
def fbTable (D : Array Nat) (K : Nat) : Array Nat × Array Nat :=
  go 0 0 0 (Array.emptyWithCapacity (K + 1)) (Array.emptyWithCapacity (K + 1)) (K + 1)
where
  go (j s0 pp : Nat) (S0 PP : Array Nat) : Nat → Array Nat × Array Nat
    | 0 => (S0, PP)
    | f + 1 =>
      let s0' := s0 + D[j]!
      go (j + 1) s0' (pp + ((s0' + 1048575) >>> 20)) (S0.push s0') (PP.push pp) f

/-- Upper P-value of `FB(c) = E[(τ_B − c)^+]` for `c = cP/2^62 ≥ 0`, given the tables
`(S0, PP) = fbTable D K` of the B state (`K < D.size`):
* if `k0 = ⌊c⌋ < S0.size`: `EB − c + Σ_{T ≤ k0} (c − T)·D[T] + c·lost`, computed as
  `EB + 2^20·PP[k0] + ⌈frac·S0[k0]⌉ + ⌈c·lost⌉ − c` (`frac = c − k0`); valid because `c < N`;
* otherwise `EB` (valid for every `c ≥ 0`, since `(τ_B − c)^+ ≤ τ_B`). -/
def fbUp (EB lost : Nat) (S0 PP : Array Nat) (cP : Nat) : Nat :=
  let k0 := cP / ONE
  if k0 < S0.size then
    let fr := cP % ONE
    EB + (PP[k0]! <<< 20) + mulUp fr S0[k0]! + mulUp cP lost - cP
  else EB

/-- `G` in the case `u < t` (the "FB case"): upper P-value of
`G(τ, u) = E_B[(u + (τ_B − 1)·τ/(p−1) − t)^+] = (τ/(p−1))·FB(c)`, `c = 1 + (t − u)(p−1)/τ`,
with `t = dn/10^9`, `u = uNum/uDen` (`uNum·10^9 < dn·uDen`) and `τ ≥ 1`.
`c` is rounded down to a P-value (FB is nonincreasing in `c`), the product rounded up. -/
def gUp (fb : Nat → Nat) (dn p τ uNum uDen : Nat) : Nat :=
  let num := (dn * uDen - uNum * DDEN) * (p - 1)
  let cP := ONE + num * ONE / (DDEN * uDen * τ)
  cdiv (τ * fb cP) (p - 1)

end MinModulus.CheckerImpl
