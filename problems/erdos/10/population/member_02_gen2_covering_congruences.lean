/-
  Population Member 02 (Gen 2): Covering congruences and Romanov's theorem

  Approach:
  1. Define R_k(n) = number of representations of n as p + Σ_{i=1}^{k} 2^{e_i}
     (prime + sum of at most k powers of two).
  2. Show via sieve bounds that the set of integers not representable
     with k powers of two has upper density at most f(k) → 0.
  3. Use a covering congruence system (Erdős–Selfridge style) to show
     that if k is too small, the uncovered set has positive lower density.
  4. The gap between the upper bound (from sieve) and the lower bound
     (from covering) narrows as k grows. The conjecture asks whether
     there exists k where the lower bound vanishes.

  Key lemmas:
  - Romanov's theorem: |{n ≤ N : n = p + 2^k}| ~ c·N for some c > 0.
  - For a fixed k, |{n ≤ N : n = p + Σ_{i=1}^{k} 2^{e_i}}| ≤ C_k·N / log N.
  - Covering system: residues a_i mod m_i such that every large integer
    satisfies n ≡ a_i (mod m_i) for some i, and for each residue,
    some congruence blocks n - 2^{e} from being prime.

  Rating (initial): Elo 1250
-/

import Mathlib

open Set Finset
open scoped BigOperators

namespace Erdos10

/-- n can be written as a prime plus a distinct sum of at most k powers of two. -/
def RepresentableWith (n : ℕ) (k : ℕ) : Prop :=
  ∃ (p : ℕ) (S : Finset ℕ), Nat.Prime p ∧ p ≤ n ∧ S.card ≤ k ∧
    (∑ e in S, 2^e) ≤ n - p ∧
    (∑ e in S, 2^e) + p = n

/-- The main conjecture: there exists k such that every sufficiently large
    integer n is representable with at most k powers of two. -/
def MainConjecture : Prop :=
  ∃ (k : ℕ), ∀ᶠ (n : ℕ) in Filter.atTop, RepresentableWith n k

/-- The representation function: number of ways to write n as p + 2^e. -/
def r (n : ℕ) : ℕ :=
  (Finset.filter (λ (p : ℕ) => Nat.Prime p ∧ ∃ (e : ℕ), p + 2^e = n)
    (Finset.range (n+1))).card

/-- The representation function for at most k powers of two. -/
def r_k (n : ℕ) (k : ℕ) : ℕ :=
  (Finset.filter (λ (S : Finset ℕ) => S.card ≤ k ∧ (∃ p : ℕ, Nat.Prime p ∧ p + (∑ e in S, 2^e) = n))
    (Finset.powerset (Finset.range n))).card

/-- For k=1, Romanov's theorem gives positive density. -/
lemma romanov_positive_density : ∃ (c : ℝ), c > 0 ∧
    ∀ᶠ (N : ℕ) in Filter.atTop,
      ((Finset.filter (λ n => r n ≥ 1) (Finset.range N)).card : ℝ) / (N : ℝ) ≥ c := by
  sorry

/-- For fixed k, the average of r_k(n) is bounded by C_k / log n.
    (Sieve bound: a number can be represented in at most ~k! ways.) -/
lemma r_k_average_bound (k : ℕ) : ∃ (C : ℝ), ∀ n, (r_k n k : ℝ) ≤ C := by
  sorry

/-- If k exists, the conjecture is true. Conversely, if for every k
    the uncovered set has positive lower density, then the conjecture is false. -/
lemma equivalence : MainConjecture ↔
    ∃ (k : ℕ), ¬ ∃ (δ : ℝ), δ > 0 ∧
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ((Finset.filter (λ n => ¬ RepresentableWith n k) (Finset.range N)).card : ℝ) / (N : ℝ) ≥ δ := by
  sorry

-- EVOLVE-BLOCK-START

/-- A covering system approach: if we can construct a finite set of
    congruences that "covers" all integers, and for each congruence class
    we block the representation p + 2^e, then the conjecture fails for that k.

    This is analogous to Erdős's covering system for the n = p + 2^k problem. -/
lemma covering_system_blocks_k (k : ℕ) : (∃ (A : Finset (ℕ × ℕ)),
    (∀ n : ℕ, ∃ (a : ℕ) (m : ℕ), (a, m) ∈ A ∧ n ≡ a [MOD m]) ∧
    (∀ (a, m) ∈ A, ∀ (e : ℕ) (p : ℕ), Nat.Prime p → p + 2^e ≢ a [MOD m])) →
    ¬ MainConjecture := by
  sorry

/-- Attempt to construct a covering system for small k.
    For k = 1, the covering system {0 mod 2, 0 mod 3, 1 mod 4, 5 mod 8, ...}
    blocks all representations. For k > 1, more moduli are needed. -/
lemma covering_system_exists (k : ℕ) : (∃ (A : Finset (ℕ × ℕ)),
    (∀ n : ℕ, ∃ (a : ℕ) (m : ℕ), (a, m) ∈ A ∧ n ≡ a [MOD m]) ∧
    (∀ (a, m) ∈ A, ∀ (e : ℕ) (p : ℕ), Nat.Prime p → p + 2^e ≢ a [MOD m])) := by
  sorry

-- EVOLVE-BLOCK-END

end Erdos10
