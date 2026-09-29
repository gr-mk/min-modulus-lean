import MinModulus.CheckerImpl.Arith
/-
# `MinModulus.CheckerImpl.Primes` — primes by trial division and a sieve

Status: complete, no `sorry`. Core Lean only.

* Primes `≤ PX` (where every prime gets its own bound) come from **trial division**
  (`isPrimeTD`), so that list is exactly the list of primes.
* For `PX < p ≤ PMAX` only *counts* of primes in blocks are needed, and an upper bound
  suffices. They come from a sieve in a `ByteArray` in which an index is marked only
  when it is a product `i * j` with `2 ≤ i ≤ j`; hence **every prime is unmarked** and
  `countUnmarked` is an upper bound on the number of primes in a range.
-/
namespace MinModulus.CheckerImpl

/-- Trial-division helper: `true` iff no `d' ∈ [d, d + fuel)` with `d'·d' ≤ n` divides `n`
(stops early, returning `true`, once `d·d > n`). -/
def noDivisorFrom (n d : Nat) : Nat → Bool
  | 0 => true
  | f + 1 => if n < d * d then true else if n % d == 0 then false else noDivisorFrom n (d + 1) f

/-- `isPrimeTD n = true` iff `n` is prime (`n ≥ 2` and no divisor in `[2, √n]`). -/
def isPrimeTD (n : Nat) : Bool := 2 ≤ n && noDivisorFrom n 2 n

/-- All primes `≤ P`, increasing (trial division on every `n ∈ [2, P]`). -/
def primesUpTo (P : Nat) : Array Nat := go 2 (P - 1) #[]
where
  go (n : Nat) : Nat → Array Nat → Array Nat
    | 0, acc => acc
    | f + 1, acc => go (n + 1) f (if isPrimeTD n then acc.push n else acc)

/-- A `ByteArray` of `n` zero bytes. -/
def zeroBytes (n : Nat) : ByteArray := go n (ByteArray.emptyWithCapacity n)
where
  go : Nat → ByteArray → ByteArray
    | 0, b => b
    | k + 1, b => go k (b.push 0)

/-- Marks the indices `j, j + i, j + 2i, …` that are `≤ N` (at most `fuel` of them).
Called with `j = i * i`, so every marked index is `i * (i + r)` for some `r ≥ 0`. -/
def markFrom (c : ByteArray) (i j N : Nat) : Nat → ByteArray
  | 0 => c
  | f + 1 => if j ≤ N then markFrom (c.set! j 1) i (j + i) N f else c

/-- Outer sieve loop over `i = 2, 3, …` while `i * i ≤ N`. -/
def sieveOuter (N : Nat) (c : ByteArray) (i : Nat) : Nat → ByteArray
  | 0 => c
  | f + 1 =>
    if i * i ≤ N then
      sieveOuter N (if c.get! i == 0 then markFrom c i (i * i) N (N + 1) else c) (i + 1) f
    else c

/-- Sieve of Eratosthenes on `[0, N]` (size `N + 1`). **Soundness property:** an entry is
set to `1` only at an index `i * (i + r)` with `i ≥ 2`, so every prime `≤ N` has entry `0`.
(In fact exactly the composites `≤ N` are marked.) -/
def sieve (N : Nat) : ByteArray := sieveOuter N (zeroBytes (N + 1)) 2 (N + 1)

/-- Number of unmarked indices in `[a, b)` (all `< c.size`). Upper bound for the number of
primes in `[a, b)` when `c = sieve N`, `b ≤ N + 1`. -/
def countUnmarked (c : ByteArray) (a b : Nat) : Nat := go a (b - a) 0
where
  go (i : Nat) : Nat → Nat → Nat
    | 0, acc => acc
    | f + 1, acc => go (i + 1) f (if c.get! i == 0 then acc + 1 else acc)

end MinModulus.CheckerImpl
