import MinModulus.CheckerMath.FirstMoment
import MinModulus.CheckerMath.Moment

/-!
# CheckerMath: certificate glue and the δ schedule

STATUS: complete, no `sorry`. Owned by the CheckerMath (first moment / moments / glue) agent.

This file turns the outputs of an executable checker into the fields of `Main.Cert`.

## Assembling a certificate
`Cert m X δ c T` follows from (`cert_of_bounds`; `cert_of_pair` / `cert_of_check` / `cert_of_rat`
for the checker's data):
* the δ fields, for the pair-valued schedule `δ = deltaPairR f` with
  `f = CheckerImpl.deltaCert P` (`(deltaN P p, 10^9)` for `p ≤ X`, `(1, 2)` for `p > X`):
  `deltaPairR_nonneg`, `deltaPairR_le_half` (from `2·deltaN ≤ 10^9`), `deltaPairR_tail`;
  the tilt is exact, `tilt_deltaPairR : tilt = 10^9/(10^9 - dn)` (the checker never rounds `ν`);
* the per-prime bounds `∀ p ≤ X prime, ∀ N, hingeLoss m δ p (fun _ => N) ≤ c p`
  (`FirstMoment`, `Moment`, and the comparison-bound layer), with
  `c p = costOf (run P) P p / 2^62`;
* `Σ_{p ≤ X prime} c p ≤ (etaA + etaB + etaC)/2^62`: `sum_primesLE_le_split` (primes `≤ PX`,
  then the blocks `[start, stop)` with `count ≥ #primes` and per-prime value `val`);
* `T ≥ Π_{q ≤ X prime} tailFactor δ q`: `prod_primesLE_le_split` with `tailFactor_le_block`
  (per prime: `Q = q`; blocks: `Q` = block start, as in `fac2 B dn`);
* the final test of `CheckerImpl.checkWith_spec`, `etaA + etaB + etaC + cdiv (T·100) (189 X) < 2^62`:
  `real_total_lt_of_check` (also `real_total_lt_of_nat`, `real_total_lt_of_rat`).

## Loop invariants for a loop over consecutive blocks `[P, P')`
`sum_primesBelow_le_add` : `Σ_{q<P'} c ≤ Σ_{q<P} c + n·a`;
`prod_primesBelow_le_mul_pow` : `Π_{q<P'} f ≤ (Π_{q<P} f)·F^n` (`#primes in [P,P') ≤ n`,
`c ≤ a`, `f ≤ F` there); `sum_primesBelow_mono`, `prod_primesBelow_mono` to change a range.
Note `Nat.primesLE X = Nat.primesBelow (X + 1)` (definitional).

## Covering lemmas (`sum_le_of_cover`, `prod_le_of_cover`)
Index set `I`, blocks `blk i`, multiplicities `n i ≥ #(primes in the block)`, costs `a i ≥ c p`
(factors `F i ≥ f p`) on the block. Soundness needs only: **every prime is in some block**,
costs `≥ 0` (for sums), factors `≥ 1` (for products). Extra entries, overlapping blocks and
non-primes in the blocks are harmless. `sum_primesLE_le_list` / `prod_primesLE_le_list` for lists.
-/

namespace MinModulus.CheckerMath

open Finset MinModulus.Smooth MinModulus.Main

/-! ### Assembling the certificate -/

/-- **Certificate assembly.** The fields of `Cert`, with `total_lt` replaced by an upper bound
`S` for `Σ_{p ≤ X} c p` and the final inequality `S + T · 100/(189 X) < 1`. -/
theorem cert_of_bounds {m X : ℕ} (hX : 2 ^ 27 ≤ X) {δ : ℕ → ℝ}
    (hδ0 : ∀ p, p.Prime → 0 ≤ δ p) (hδ1 : ∀ p, p.Prime → δ p ≤ 1 / 2)
    (hδX : ∀ p, p.Prime → X < p → δ p = 1 / 2) {c : ℕ → ℝ}
    (hloss : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ, hingeLoss m δ p (fun _ => N) ≤ c p)
    {S T : ℝ} (hS : ∑ p ∈ Nat.primesLE X, c p ≤ S)
    (hT : ∏ q ∈ Nat.primesLE X, tailFactor δ q ≤ T)
    (hST : S + T * (100 / (189 * (X : ℝ))) < 1) : Cert m X δ c T where
  two_pow_le := hX
  delta_nonneg := hδ0
  delta_le_half := hδ1
  delta_tail := hδX
  loss_le := hloss
  prod_le := hT
  total_lt := by linarith

/-! ### From a decidable check to the real inequality -/

/-- The final inequality for rational data: a `decide`/`native_decide`-checkable statement about
`ℚ` gives the real one. -/
theorem real_total_lt_of_rat {S T : ℚ} {X : ℕ} (h : S + T * (100 / (189 * X)) < 1) :
    (S : ℝ) + (T : ℝ) * (100 / (189 * (X : ℝ))) < 1 := by
  have := (Rat.cast_lt (K := ℝ)).2 h
  push_cast at this
  exact this

/-- The final inequality for fixed-point data `S = e/K`, `T = t/K` (e.g. `K = 2^62`): it follows
from the natural-number inequality `e · 189 X + t · 100 < 189 X K`. -/
theorem real_total_lt_of_nat {e t X K : ℕ} (hK : 0 < K) (hX : 0 < X)
    (h : e * (189 * X) + t * 100 < 189 * X * K) :
    (e : ℝ) / K + ((t : ℝ) / K) * (100 / (189 * (X : ℝ))) < 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  have h' : (e : ℝ) * (189 * X) + t * 100 < 189 * X * K := by exact_mod_cast h
  have e1 : (e : ℝ) / K + ((t : ℝ) / K) * (100 / (189 * (X : ℝ))) =
      ((e : ℝ) * (189 * X) + t * 100) / (189 * X * K) := by
    field_simp
  rw [e1, div_lt_one (by positivity)]
  exact h'

/-- `Bool` form of `real_total_lt_of_nat`. -/
theorem real_total_lt_of_nat_decide {e t X K : ℕ} (hK : 0 < K) (hX : 0 < X)
    (h : decide (e * (189 * X) + t * 100 < 189 * X * K) = true) :
    (e : ℝ) / K + ((t : ℝ) / K) * (100 / (189 * (X : ℝ))) < 1 :=
  real_total_lt_of_nat hK hX (of_decide_eq_true h)

/-! ### Covering lemmas: sums and products over the primes, from a checker's loop -/

/-- **Sums over a covered set.** If every `p ∈ S` lies in some block `blk i` (`i ∈ I`), `c ≥ 0`
on `S`, `c p ≤ a i` for `p ∈ S ∩ blk i`, and `#(S ∩ blk i) ≤ n i`, then
`Σ_{p ∈ S} c p ≤ Σ_{i ∈ I} n i · a i`. -/
theorem sum_le_of_cover {ι : Type*} (S : Finset ℕ) (I : Finset ι) (blk : ι → Finset ℕ)
    (n : ι → ℕ) (a : ι → ℝ) (c : ℕ → ℝ) (hc0 : ∀ p ∈ S, 0 ≤ c p)
    (hcov : ∀ p ∈ S, ∃ i ∈ I, p ∈ blk i)
    (hca : ∀ i ∈ I, ∀ p ∈ S, p ∈ blk i → c p ≤ a i)
    (hn : ∀ i ∈ I, #(S.filter (· ∈ blk i)) ≤ n i) (ha0 : ∀ i ∈ I, 0 ≤ a i) :
    ∑ p ∈ S, c p ≤ ∑ i ∈ I, (n i : ℝ) * a i := by
  classical
  calc ∑ p ∈ S, c p ≤ ∑ p ∈ S, ∑ i ∈ I, (if p ∈ blk i then c p else 0) := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨i, hi, hpi⟩ := hcov p hp
        rw [← sum_filter]
        exact single_le_sum (f := fun _ => c p) (fun _ _ => hc0 p hp) (mem_filter.2 ⟨hi, hpi⟩)
    _ = ∑ i ∈ I, ∑ p ∈ S, (if p ∈ blk i then c p else 0) := sum_comm
    _ = ∑ i ∈ I, ∑ p ∈ S.filter (· ∈ blk i), c p := by simp_rw [sum_filter]
    _ ≤ ∑ i ∈ I, #(S.filter (· ∈ blk i)) • a i :=
        sum_le_sum fun i hi => sum_le_card_nsmul _ _ _ fun p hp =>
          hca i hi p (mem_filter.1 hp).1 (mem_filter.1 hp).2
    _ ≤ ∑ i ∈ I, (n i : ℝ) * a i := sum_le_sum fun i hi => by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn i hi) (ha0 i hi)

/-- **Products over a covered set.** If every `q ∈ S` lies in some block `blk i` (`i ∈ I`),
`f ≥ 1` on `S`, `f q ≤ F i` for `q ∈ S ∩ blk i`, `#(S ∩ blk i) ≤ n i` and `F i ≥ 1`, then
`Π_{q ∈ S} f q ≤ Π_{i ∈ I} (F i)^(n i)`. -/
theorem prod_le_of_cover {ι : Type*} (S : Finset ℕ) (I : Finset ι) (blk : ι → Finset ℕ)
    (n : ι → ℕ) (F : ι → ℝ) (f : ℕ → ℝ) (hf1 : ∀ q ∈ S, 1 ≤ f q)
    (hcov : ∀ q ∈ S, ∃ i ∈ I, q ∈ blk i)
    (hfF : ∀ i ∈ I, ∀ q ∈ S, q ∈ blk i → f q ≤ F i)
    (hn : ∀ i ∈ I, #(S.filter (· ∈ blk i)) ≤ n i) (hF1 : ∀ i ∈ I, 1 ≤ F i) :
    ∏ q ∈ S, f q ≤ ∏ i ∈ I, F i ^ n i := by
  classical
  calc ∏ q ∈ S, f q ≤ ∏ q ∈ S, ∏ i ∈ I, (if q ∈ blk i then f q else 1) := by
        refine prod_le_prod₀ (fun q hq => zero_le_one.trans (hf1 q hq)) fun q hq => ?_
        obtain ⟨i, hi, hqi⟩ := hcov q hq
        rw [← prod_filter, prod_const]
        have hpos : 1 ≤ #(I.filter (fun j => q ∈ blk j)) :=
          card_pos.2 ⟨i, mem_filter.2 ⟨hi, hqi⟩⟩
        calc f q = f q ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ (hf1 q hq) hpos
    _ = ∏ i ∈ I, ∏ q ∈ S, (if q ∈ blk i then f q else 1) := prod_comm
    _ = ∏ i ∈ I, ∏ q ∈ S.filter (· ∈ blk i), f q := by simp_rw [prod_filter]
    _ ≤ ∏ i ∈ I, F i ^ #(S.filter (· ∈ blk i)) := by
        refine prod_le_prod₀ (fun i _ => prod_nonneg fun q hq =>
          zero_le_one.trans (hf1 q (mem_filter.1 hq).1)) fun i hi => ?_
        rw [← prod_const]
        exact prod_le_prod₀ (fun q hq => zero_le_one.trans (hf1 q (mem_filter.1 hq).1))
          fun q hq => hfF i hi q (mem_filter.1 hq).1 (mem_filter.1 hq).2
    _ ≤ ∏ i ∈ I, F i ^ n i :=
        prod_le_prod₀ (fun i hi => pow_nonneg (zero_le_one.trans (hF1 i hi)) _)
          fun i hi => pow_le_pow_right₀ (hF1 i hi) (hn i hi)

/-- **Per-entry loops.** If every `p ∈ S` is some entry `e i` (`i ∈ I`) and the costs of the
entries are `≥ 0`, then `Σ_{p ∈ S} c p ≤ Σ_{i ∈ I} c (e i)` (duplicate entries and entries
outside `S` are harmless). -/
theorem sum_le_sum_of_entries {ι : Type*} (S : Finset ℕ) (I : Finset ι) (e : ι → ℕ)
    (c : ℕ → ℝ) (hc0 : ∀ i ∈ I, 0 ≤ c (e i)) (hcov : ∀ p ∈ S, ∃ i ∈ I, e i = p) :
    ∑ p ∈ S, c p ≤ ∑ i ∈ I, c (e i) := by
  classical
  have h := sum_le_of_cover S I (fun i => {e i}) (fun _ => 1) (fun i => c (e i)) c
    (fun p hp => by obtain ⟨i, hi, rfl⟩ := hcov p hp; exact hc0 i hi)
    (fun p hp => by obtain ⟨i, hi, rfl⟩ := hcov p hp; exact ⟨i, hi, mem_singleton_self _⟩)
    (fun i _ p _ hp => by rw [mem_singleton.1 hp])
    (fun i _ => by
      refine card_le_one.2 fun a ha b hb => ?_
      rw [mem_singleton.1 (mem_filter.1 ha).2, mem_singleton.1 (mem_filter.1 hb).2])
    hc0
  simpa using h

/-- **Lists** (the checker's candidate list, e.g. the unmarked entries of a sieve): if every
prime `≤ X` occurs in `L` and the costs of the entries of `L` are `≥ 0`, then
`Σ_{p ≤ X prime} c p ≤ Σ_{p ∈ L} c p`. -/
theorem sum_primesLE_le_list (X : ℕ) (L : List ℕ) (c : ℕ → ℝ) (hc : ∀ p ∈ L, 0 ≤ c p)
    (hL : ∀ p, p.Prime → p ≤ X → p ∈ L) : ∑ p ∈ Nat.primesLE X, c p ≤ (L.map c).sum := by
  classical
  calc ∑ p ∈ Nat.primesLE X, c p ≤ ∑ p ∈ L.toFinset, c p := by
        refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ =>
          hc p (List.mem_toFinset.1 hp)
        rw [Nat.mem_primesLE] at hp
        exact List.mem_toFinset.2 (hL p hp.2 hp.1)
    _ ≤ (L.map c).sum := by
        rw [sum_list_map_count]
        refine sum_le_sum fun p hp => ?_
        have h1 : 1 ≤ L.count p := List.count_pos_iff.2 (List.mem_toFinset.1 hp)
        rw [nsmul_eq_mul]
        have h0 := hc p (List.mem_toFinset.1 hp)
        have : (1 : ℝ) ≤ L.count p := by exact_mod_cast h1
        nlinarith

/-- Product version for lists: if every prime `≤ X` occurs in `L` and `f ≥ 1` on `L`, then
`Π_{q ≤ X prime} f q ≤ Π_{q ∈ L} f q`. -/
theorem prod_primesLE_le_list (X : ℕ) (L : List ℕ) (f : ℕ → ℝ) (hf : ∀ q ∈ L, 1 ≤ f q)
    (hL : ∀ q, q.Prime → q ≤ X → q ∈ L) : ∏ q ∈ Nat.primesLE X, f q ≤ (L.map f).prod := by
  classical
  calc ∏ q ∈ Nat.primesLE X, f q ≤ ∏ q ∈ L.toFinset, f q := by
        refine prod_le_prod_of_subset_of_one_le₀ (fun q hq => ?_) ?_ fun q hq _ =>
          hf q (List.mem_toFinset.1 hq)
        · rw [Nat.mem_primesLE] at hq
          exact List.mem_toFinset.2 (hL q hq.2 hq.1)
        · exact fun q hq => zero_le_one.trans
            (hf q (hL q (Nat.mem_primesLE.1 hq).2 (Nat.mem_primesLE.1 hq).1))
    _ ≤ (L.map f).prod := by
        rw [prod_list_map_count]
        refine prod_le_prod₀ (fun q hq => zero_le_one.trans (hf q (List.mem_toFinset.1 hq)))
          fun q hq => ?_
        have h1 : 1 ≤ L.count q := List.count_pos_iff.2 (List.mem_toFinset.1 hq)
        calc f q = f q ^ 1 := (pow_one _).symm
          _ ≤ f q ^ L.count q := pow_le_pow_right₀ (hf q (List.mem_toFinset.1 hq)) h1

/-! ### Block-loop invariants over `Nat.primesBelow` -/

/-- Splitting the primes below `P'` at `P ≤ P'`. -/
theorem primesBelow_filter_lt {P P' : ℕ} (h : P ≤ P') :
    (Nat.primesBelow P').filter (· < P) = Nat.primesBelow P := by
  ext q
  simp only [mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨_, hq⟩, hqP⟩
    exact ⟨hqP, hq⟩
  · rintro ⟨hqP, hq⟩
    exact ⟨⟨lt_of_lt_of_le hqP h, hq⟩, hqP⟩

/-- **Sum loop invariant for one block `[P, P')`**: if `c q ≤ a` for the primes `q ∈ [P, P')`,
`a ≥ 0`, and there are at most `n` such primes, then
`Σ_{q < P'} c q ≤ Σ_{q < P} c q + n · a`. -/
theorem sum_primesBelow_le_add {P P' : ℕ} (hPP' : P ≤ P') (c : ℕ → ℝ) {a : ℝ}
    (ha : ∀ q ∈ Nat.primesBelow P', P ≤ q → c q ≤ a) {n : ℕ}
    (hn : #((Nat.primesBelow P').filter (P ≤ ·)) ≤ n) (ha0 : 0 ≤ a) :
    ∑ q ∈ Nat.primesBelow P', c q ≤ ∑ q ∈ Nat.primesBelow P, c q + n * a := by
  rw [← sum_filter_add_sum_filter_not (Nat.primesBelow P') (· < P), primesBelow_filter_lt hPP']
  have e : (Nat.primesBelow P').filter (fun q => ¬ q < P) = (Nat.primesBelow P').filter (P ≤ ·) :=
    filter_congr fun q _ => not_lt
  rw [e]
  have h1 : ∑ q ∈ (Nat.primesBelow P').filter (P ≤ ·), c q ≤
      #((Nat.primesBelow P').filter (P ≤ ·)) • a :=
    sum_le_card_nsmul _ _ _ fun q hq => ha q (mem_filter.1 hq).1 (mem_filter.1 hq).2
  rw [nsmul_eq_mul] at h1
  have h2 : (#((Nat.primesBelow P').filter (P ≤ ·)) : ℝ) * a ≤ n * a :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ha0
  linarith

/-- **Product loop invariant for one block `[P, P')`**: if `1 ≤ f q ≤ F` for the primes
`q ∈ [P, P')`, `f ≥ 1` below `P`, and there are at most `n` primes in `[P, P')`, then
`Π_{q < P'} f q ≤ (Π_{q < P} f q) · F^n`. -/
theorem prod_primesBelow_le_mul_pow {P P' : ℕ} (hPP' : P ≤ P') (f : ℕ → ℝ)
    (hf1 : ∀ q ∈ Nat.primesBelow P', 1 ≤ f q) {F : ℝ}
    (hF : ∀ q ∈ Nat.primesBelow P', P ≤ q → f q ≤ F) {n : ℕ}
    (hn : #((Nat.primesBelow P').filter (P ≤ ·)) ≤ n) (hF1 : 1 ≤ F) :
    ∏ q ∈ Nat.primesBelow P', f q ≤ (∏ q ∈ Nat.primesBelow P, f q) * F ^ n := by
  rw [← prod_filter_mul_prod_filter_not (Nat.primesBelow P') (· < P),
    primesBelow_filter_lt hPP']
  have e : (Nat.primesBelow P').filter (fun q => ¬ q < P) = (Nat.primesBelow P').filter (P ≤ ·) :=
    filter_congr fun q _ => not_lt
  rw [e]
  have hA : 0 ≤ ∏ q ∈ Nat.primesBelow P, f q := prod_nonneg fun q hq =>
    zero_le_one.trans (hf1 q (Nat.primesBelow_mono hPP' hq))
  refine mul_le_mul_of_nonneg_left ?_ hA
  calc ∏ q ∈ (Nat.primesBelow P').filter (P ≤ ·), f q
      ≤ ∏ _q ∈ (Nat.primesBelow P').filter (P ≤ ·), F :=
        prod_le_prod₀ (fun q hq => zero_le_one.trans (hf1 q (mem_filter.1 hq).1))
          fun q hq => hF q (mem_filter.1 hq).1 (mem_filter.1 hq).2
    _ = F ^ #((Nat.primesBelow P').filter (P ≤ ·)) := prod_const F
    _ ≤ F ^ n := pow_le_pow_right₀ hF1 hn

/-- Extending the range of a sum of nonnegative costs: `Σ_{q < a} c q ≤ Σ_{q < b} c q` for
`a ≤ b` (e.g. `Nat.primesLE X = Nat.primesBelow (X + 1)` and a last block ending beyond `X`). -/
theorem sum_primesBelow_mono {a b : ℕ} (hab : a ≤ b) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Nat.primesBelow b, a ≤ q → 0 ≤ c q) :
    ∑ q ∈ Nat.primesBelow a, c q ≤ ∑ q ∈ Nat.primesBelow b, c q :=
  sum_le_sum_of_subset_of_nonneg (Nat.primesBelow_mono hab) fun q hq hqa =>
    hc q hq (by
      by_contra h
      exact hqa (Nat.mem_primesBelow.2 ⟨not_le.1 h, Nat.prime_of_mem_primesBelow hq⟩))

/-! ### The tail factor `1 + ν(3q-1)/(q-1)²` -/

/-- `tailFactor δ q ≤ 1 + ν (3Q-1)/(Q-1)²` for `2 ≤ Q ≤ q` and a tilt bound `tilt δ q ≤ ν`
(`δ q ≤ 1`). With `Q = q` this is the per-prime bound; with `Q` a block start it serves the
whole block. -/
theorem tailFactor_le_block {δ : ℕ → ℝ} {q Q : ℕ} (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hδ : δ q ≤ 1)
    {ν : ℝ} (hν : tilt δ q ≤ ν) :
    tailFactor δ q ≤ 1 + ν * (3 * Q - 1) / ((Q : ℝ) - 1) ^ 2 := by
  unfold tailFactor
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hQ.trans hQq
  have ht0 := tilt_nonneg hδ
  have hf0 : 0 ≤ (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have h1 : tilt δ q * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 ≤
      ν * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hν hf0
  have h2 : ν * (3 * (q : ℝ) - 1) / ((q : ℝ) - 1) ^ 2 ≤
      ν * (3 * (Q : ℝ) - 1) / ((Q : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (sqFactor_anti hQ hQq) (ht0.trans hν)
  linarith

/-- The block factors are `≥ 1`: `1 ≤ 1 + ν (3Q-1)/(Q-1)²` for `ν ≥ 0`, `Q ≥ 1`. -/
theorem one_le_sqFactor {Q : ℕ} (hQ : 1 ≤ Q) {ν : ℝ} (hν : 0 ≤ ν) :
    1 ≤ 1 + ν * (3 * Q - 1) / ((Q : ℝ) - 1) ^ 2 := by
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have : 0 ≤ ν * (3 * Q - 1) / ((Q : ℝ) - 1) ^ 2 :=
    div_nonneg (mul_nonneg hν (by linarith)) (sq_nonneg _)
  linarith

/-! ### The δ schedule (aligned with `CheckerImpl.deltaCert`) -/

/-- The certificate's δ from a checker's schedule given as `(numerator, denominator)` pairs:
`deltaOfPair f p = (f p).1 / (f p).2`. For the landed checker take `f = CheckerImpl.deltaCert P`,
i.e. `(deltaN P p, 10^9)` for `p ≤ X := P.PMAX` and `(1, 2)` for `p > X`. -/
def deltaOfPair (f : ℕ → ℕ × ℕ) (p : ℕ) : ℚ := ((f p).1 : ℚ) / ((f p).2 : ℚ)

/-- The real-valued schedule used as `δ` in `Cert`. -/
noncomputable def deltaPairR (f : ℕ → ℕ × ℕ) : ℕ → ℝ := fun p => (deltaOfPair f p : ℝ)

theorem deltaPairR_apply (f : ℕ → ℕ × ℕ) (p : ℕ) :
    deltaPairR f p = ((f p).1 : ℝ) / ((f p).2 : ℝ) := by
  simp [deltaPairR, deltaOfPair]

theorem deltaPairR_of_eq {f : ℕ → ℕ × ℕ} {p dn D : ℕ} (h : f p = (dn, D)) :
    deltaPairR f p = (dn : ℝ) / D := by
  rw [deltaPairR_apply, h]

/-- `Cert.delta_nonneg` for the schedule (no hypothesis). -/
theorem deltaPairR_nonneg (f : ℕ → ℕ × ℕ) : ∀ p, p.Prime → 0 ≤ deltaPairR f p := fun p _ => by
  rw [deltaPairR_apply]
  positivity

/-- `Cert.delta_le_half` for the schedule, from `2 · num ≤ den` (for `deltaCert`: `deltaN ≤ 0.45·10^9`
below `X`, and `(1, 2)` above). -/
theorem deltaPairR_le_half {f : ℕ → ℕ × ℕ} (hf : ∀ p, p.Prime → 2 * (f p).1 ≤ (f p).2) :
    ∀ p, p.Prime → deltaPairR f p ≤ 1 / 2 := fun p hp => by
  rw [deltaPairR_apply]
  have h : (2 : ℝ) * (f p).1 ≤ (f p).2 := by exact_mod_cast hf p hp
  rcases Nat.eq_zero_or_pos (f p).2 with h0 | hpos
  · rw [h0]
    simp
  · have hpos' : (0 : ℝ) < (f p).2 := by exact_mod_cast hpos
    rw [div_le_iff₀ hpos']
    linarith

/-- `Cert.delta_tail` for the schedule. -/
theorem deltaPairR_tail {f : ℕ → ℕ × ℕ} {X : ℕ} (hf : ∀ p, p.Prime → X < p → f p = (1, 2)) :
    ∀ p, p.Prime → X < p → deltaPairR f p = 1 / 2 := fun p hp hXp => by
  rw [deltaPairR_of_eq (hf p hp hXp)]
  norm_num

/-- The exact tilt: `f p = (dn, D)`, `dn < D` ⟹ `tilt = D/(D - dn)` (the checker's
`ν = 10^9/(10^9 - dn)`, never rounded). -/
theorem tilt_deltaPairR {f : ℕ → ℕ × ℕ} {p dn D : ℕ} (h : f p = (dn, D)) (hdn : dn < D) :
    tilt (deltaPairR f) p = (D : ℝ) / ((D : ℝ) - dn) := by
  unfold tilt
  rw [deltaPairR_of_eq h]
  have hD : (dn : ℝ) < D := by exact_mod_cast hdn
  have hD0 : (0 : ℝ) < D := lt_of_le_of_lt (Nat.cast_nonneg dn) hD
  field_simp

/-- `1 - δ_p = (D - dn)/D` for `f p = (dn, D)`, `0 < D`. -/
theorem one_sub_deltaPairR {f : ℕ → ℕ × ℕ} {p dn D : ℕ} (h : f p = (dn, D)) (hD : 0 < D) :
    1 - deltaPairR f p = ((D : ℝ) - dn) / D := by
  rw [deltaPairR_of_eq h]
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  field_simp

/-- When `f p = (0, D)` (no distortion at `p`), `δ_p = 0` and the tilt is `1`. -/
theorem deltaPairR_eq_zero {f : ℕ → ℕ × ℕ} {p D : ℕ} (h : f p = (0, D)) : deltaPairR f p = 0 := by
  rw [deltaPairR_of_eq h]
  simp

theorem tilt_deltaPairR_of_zero {f : ℕ → ℕ × ℕ} {p D : ℕ} (h : f p = (0, D)) :
    tilt (deltaPairR f) p = 1 :=
  tilt_eq_one_of_eq_zero (deltaPairR_eq_zero h)

/-! ### The checker's final inequality (`CheckerImpl.checkWith_spec`) -/

/-- `a ≤ ⌈a/b⌉·b` for the ceiling `(a + b - 1)/b` (= `CheckerImpl.cdiv a b`), `b > 0`. -/
theorem le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ (a + b - 1) / b * b := by
  have h := Nat.lt_mul_div_succ (a + b - 1) hb
  rw [Nat.mul_succ, Nat.mul_comm] at h
  omega

/-- **The checker's Bool → the real inequality.** `checkWith_spec` gives
`etaA + etaB + etaC + cdiv (T·100) (189·X) < 2^62`; with `e = etaA + etaB + etaC` this is the
hypothesis below (`cdiv a b = (a + b - 1)/b` definitionally), and the conclusion is the real
inequality for `S = e/K`, `T = t/K`. -/
theorem real_total_lt_of_check {e t X K : ℕ} (hX : 0 < X) (hK : 0 < K)
    (h : e + (t * 100 + 189 * X - 1) / (189 * X) < K) :
    (e : ℝ) / K + ((t : ℝ) / K) * (100 / (189 * (X : ℝ))) < 1 := by
  refine real_total_lt_of_nat hK hX ?_
  have h1 := le_ceilDiv_mul (a := t * 100) (b := 189 * X) (by positivity)
  have h2 : (e + (t * 100 + 189 * X - 1) / (189 * X)) * (189 * X) < K * (189 * X) :=
    Nat.mul_lt_mul_of_pos_right h (by positivity)
  have h3 : e * (189 * X) + t * 100 ≤ (e + (t * 100 + 189 * X - 1) / (189 * X)) * (189 * X) := by
    rw [Nat.add_mul]
    omega
  calc e * (189 * X) + t * 100 < K * (189 * X) := lt_of_le_of_lt h3 h2
    _ = 189 * X * K := by ring

/-! ### Splitting the sum and the product at `PX` (per-prime loop + block loop) -/

theorem primesLE_filter_le {PX X : ℕ} (h : PX ≤ X) :
    (Nat.primesLE X).filter (· ≤ PX) = Nat.primesLE PX := by
  ext q
  simp only [mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_, hq⟩, hqP⟩
    exact ⟨hqP, hq⟩
  · rintro ⟨hqP, hq⟩
    exact ⟨⟨hqP.trans h, hq⟩, hqP⟩

/-- **Sum over the primes `≤ X`, as the checker computes it**: the primes `≤ PX` (bounded by
`S1`, e.g. `(etaA + etaB)/2^62`) plus blocks `[lo i, hi i)` covering the primes in `(PX, X]`, each
with at most `n i` primes and per-prime cost `≤ a i` (e.g. `count`, `val/2^62`):
`Σ_{p ≤ X} c p ≤ S1 + Σ_i n i · a i`. -/
theorem sum_primesLE_le_split {PX X : ℕ} (hPX : PX ≤ X) (c : ℕ → ℝ) {S1 : ℝ}
    (h1 : ∑ p ∈ Nat.primesLE PX, c p ≤ S1) {ι : Type*} (I : Finset ι) (lo hi n : ι → ℕ)
    (a : ι → ℝ) (hc0 : ∀ p ∈ Nat.primesLE X, PX < p → 0 ≤ c p)
    (hcov : ∀ p ∈ Nat.primesLE X, PX < p → ∃ i ∈ I, lo i ≤ p ∧ p < hi i)
    (hca : ∀ i ∈ I, ∀ p ∈ Nat.primesLE X, PX < p → lo i ≤ p → p < hi i → c p ≤ a i)
    (hn : ∀ i ∈ I, #((Ico (lo i) (hi i)).filter Nat.Prime) ≤ n i) (ha0 : ∀ i ∈ I, 0 ≤ a i) :
    ∑ p ∈ Nat.primesLE X, c p ≤ S1 + ∑ i ∈ I, (n i : ℝ) * a i := by
  classical
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE X) (· ≤ PX), primesLE_filter_le hPX]
  have h2 := sum_le_of_cover ((Nat.primesLE X).filter (fun p => ¬ p ≤ PX)) I
    (fun i => Ico (lo i) (hi i)) n a c
    (fun p hp => hc0 p (mem_filter.1 hp).1 (not_le.1 (mem_filter.1 hp).2))
    (fun p hp => by
      obtain ⟨i, hi, h1, h2⟩ := hcov p (mem_filter.1 hp).1 (not_le.1 (mem_filter.1 hp).2)
      exact ⟨i, hi, mem_Ico.2 ⟨h1, h2⟩⟩)
    (fun i hi p hp hpi => hca i hi p (mem_filter.1 hp).1 (not_le.1 (mem_filter.1 hp).2)
      (mem_Ico.1 hpi).1 (mem_Ico.1 hpi).2)
    (fun i hi => by
      refine le_trans (card_le_card fun p hp => ?_) (hn i hi)
      rw [mem_filter] at hp ⊢
      exact ⟨hp.2, Nat.prime_of_mem_primesLE (mem_filter.1 hp.1).1⟩)
    ha0
  linarith

/-- **Product over the primes `≤ X`, as the checker computes it**: `T1 ≥ Π_{q ≤ PX} f q`, and blocks
`[lo i, hi i)` covering `(PX, X]` with at most `n i` primes and factors `f q ≤ F i` there
(`f ≥ 1`, `F ≥ 1`): `Π_{q ≤ X} f q ≤ T1 · Π_i (F i)^(n i)`. -/
theorem prod_primesLE_le_split {PX X : ℕ} (hPX : PX ≤ X) (f : ℕ → ℝ)
    (hf1 : ∀ q ∈ Nat.primesLE X, 1 ≤ f q) {T1 : ℝ} (h1 : ∏ q ∈ Nat.primesLE PX, f q ≤ T1)
    {ι : Type*} (I : Finset ι) (lo hi n : ι → ℕ) (F : ι → ℝ)
    (hcov : ∀ q ∈ Nat.primesLE X, PX < q → ∃ i ∈ I, lo i ≤ q ∧ q < hi i)
    (hfF : ∀ i ∈ I, ∀ q ∈ Nat.primesLE X, PX < q → lo i ≤ q → q < hi i → f q ≤ F i)
    (hn : ∀ i ∈ I, #((Ico (lo i) (hi i)).filter Nat.Prime) ≤ n i) (hF1 : ∀ i ∈ I, 1 ≤ F i) :
    ∏ q ∈ Nat.primesLE X, f q ≤ T1 * ∏ i ∈ I, F i ^ n i := by
  classical
  rw [← prod_filter_mul_prod_filter_not (Nat.primesLE X) (· ≤ PX), primesLE_filter_le hPX]
  have h2 := prod_le_of_cover ((Nat.primesLE X).filter (fun q => ¬ q ≤ PX)) I
    (fun i => Ico (lo i) (hi i)) n F f
    (fun q hq => hf1 q (mem_filter.1 hq).1)
    (fun q hq => by
      obtain ⟨i, hi, h1, h2⟩ := hcov q (mem_filter.1 hq).1 (not_le.1 (mem_filter.1 hq).2)
      exact ⟨i, hi, mem_Ico.2 ⟨h1, h2⟩⟩)
    (fun i hi q hq hqi => hfF i hi q (mem_filter.1 hq).1 (not_le.1 (mem_filter.1 hq).2)
      (mem_Ico.1 hqi).1 (mem_Ico.1 hqi).2)
    (fun i hi => by
      refine le_trans (card_le_card fun q hq => ?_) (hn i hi)
      rw [mem_filter] at hq ⊢
      exact ⟨hq.2, Nat.prime_of_mem_primesLE (mem_filter.1 hq.1).1⟩)
    hF1
  have hA0 : 0 ≤ ∏ q ∈ Nat.primesLE PX, f q := prod_nonneg fun q hq =>
    zero_le_one.trans (hf1 q (Nat.primesLE_mono hPX hq))
  have hB0 : 0 ≤ ∏ q ∈ (Nat.primesLE X).filter (fun q => ¬ q ≤ PX), f q := prod_nonneg
    fun q hq => zero_le_one.trans (hf1 q (mem_filter.1 hq).1)
  calc (∏ q ∈ Nat.primesLE PX, f q) * ∏ q ∈ (Nat.primesLE X).filter (fun q => ¬ q ≤ PX), f q
      ≤ T1 * ∏ q ∈ (Nat.primesLE X).filter (fun q => ¬ q ≤ PX), f q :=
        mul_le_mul_of_nonneg_right h1 hB0
    _ ≤ T1 * ∏ i ∈ I, F i ^ n i :=
        mul_le_mul_of_nonneg_left h2 (hA0.trans h1)

/-- Products of factors `≥ 1` grow with the range: `Π_{q < a} f ≤ Π_{q < b} f` for `a ≤ b`
(e.g. from the primes below `p` to the primes below the end of `p`'s block). -/
theorem prod_primesBelow_mono {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℝ)
    (hf : ∀ q ∈ Nat.primesBelow b, 1 ≤ f q) :
    ∏ q ∈ Nat.primesBelow a, f q ≤ ∏ q ∈ Nat.primesBelow b, f q :=
  prod_le_prod_of_subset_of_one_le₀ (Nat.primesBelow_mono hab)
    (fun q hq => zero_le_one.trans (hf q (Nat.primesBelow_mono hab hq)))
    fun q hq _ => hf q hq

/-! ### Assembling a certificate from the checker's data -/

/-- **Certificate from a pair-valued schedule** (`f = CheckerImpl.deltaCert P`): the δ fields are
discharged from `2·num ≤ den` and `f p = (1, 2)` beyond `X`. -/
theorem cert_of_pair {m X : ℕ} (hX : 2 ^ 27 ≤ X) (f : ℕ → ℕ × ℕ)
    (hf2 : ∀ p, p.Prime → 2 * (f p).1 ≤ (f p).2) (hfX : ∀ p, p.Prime → X < p → f p = (1, 2))
    {c : ℕ → ℝ}
    (hloss : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ, hingeLoss m (deltaPairR f) p (fun _ => N) ≤ c p)
    {S T : ℝ} (hS : ∑ p ∈ Nat.primesLE X, c p ≤ S)
    (hT : ∏ q ∈ Nat.primesLE X, tailFactor (deltaPairR f) q ≤ T)
    (hST : S + T * (100 / (189 * (X : ℝ))) < 1) : Cert m X (deltaPairR f) c T :=
  cert_of_bounds hX (deltaPairR_nonneg f) (deltaPairR_le_half hf2) (deltaPairR_tail hfX) hloss
    hS hT hST

/-- **Certificate in the checker's fixed-point form.** Costs `c p = cost p / K` and `T = t / K`
(`K = 2^62`), total cost numerator `e` with `Σ_{p ≤ X} cost p / K ≤ e / K`, and the checker's
final test `e + cdiv (t·100) (189 X) < K`. -/
theorem cert_of_check {m X : ℕ} (hX : 2 ^ 27 ≤ X) (f : ℕ → ℕ × ℕ)
    (hf2 : ∀ p, p.Prime → 2 * (f p).1 ≤ (f p).2) (hfX : ∀ p, p.Prime → X < p → f p = (1, 2))
    (cost : ℕ → ℕ) {K : ℕ} (hK : 0 < K)
    (hloss : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ,
      hingeLoss m (deltaPairR f) p (fun _ => N) ≤ (cost p : ℝ) / K)
    {e t : ℕ} (hS : ∑ p ∈ Nat.primesLE X, (cost p : ℝ) / K ≤ (e : ℝ) / K)
    (hT : ∏ q ∈ Nat.primesLE X, tailFactor (deltaPairR f) q ≤ (t : ℝ) / K)
    (hcheck : e + (t * 100 + 189 * X - 1) / (189 * X) < K) :
    Cert m X (deltaPairR f) (fun p => (cost p : ℝ) / K) ((t : ℝ) / K) :=
  cert_of_pair hX f hf2 hfX hloss hS hT
    (real_total_lt_of_check (lt_of_lt_of_le (by norm_num) hX) hK hcheck)

/-- Rational-data version: `cost : ℕ → ℚ`, rational `S`, `T`, and a decidable final inequality. -/
theorem cert_of_rat {m X : ℕ} (hX : 2 ^ 27 ≤ X) (f : ℕ → ℕ × ℕ)
    (hf2 : ∀ p, p.Prime → 2 * (f p).1 ≤ (f p).2) (hfX : ∀ p, p.Prime → X < p → f p = (1, 2))
    (cost : ℕ → ℚ)
    (hloss : ∀ p, p.Prime → p ≤ X → ∀ N : ℕ,
      hingeLoss m (deltaPairR f) p (fun _ => N) ≤ (cost p : ℝ))
    (S T : ℚ) (hS : ∑ p ∈ Nat.primesLE X, (cost p : ℝ) ≤ S)
    (hT : ∏ q ∈ Nat.primesLE X, tailFactor (deltaPairR f) q ≤ T)
    (hcheck : decide (S + T * (100 / (189 * X)) < 1) = true) :
    Cert m X (deltaPairR f) (fun p => (cost p : ℝ)) (T : ℝ) :=
  cert_of_pair hX f hf2 hfX hloss hS hT (real_total_lt_of_rat (of_decide_eq_true hcheck))

end MinModulus.CheckerMath
