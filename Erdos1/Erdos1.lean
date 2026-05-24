import Mathlib
open Finset

/-!
# Erdős Problem 1: Sum-Distinct Sets

**Reference:** [erdosproblems.com/1](https://www.erdosproblems.com/1)

If $A \subseteq \{1, \ldots, N\}$ with $|A| = n$ is such that the subset sums
$\sum_{a \in S} a$ are distinct for all $S \subseteq A$ then $N \gg 2^n$.

Open, $500 prize. Tags: number theory, additive combinatorics.

## Known results
- Trivial: $N \gg 2^n / n$ (counting argument)
- Erdős–Moser (1956): $N \geq (1/4 - o(1)) \cdot 2^n / \sqrt{n}$
- Current best: $N \geq \sqrt{2/\pi} \cdot 2^n / \sqrt{n}$
- Upper bound (Bohman): $N \leq 0.22002 \cdot 2^n$
- Minimal values: n=3 → N=4, n=5 → N=13, n=9 → N=161 (OEIS A276661)
-/
namespace Erdos1

/-- A finite set of naturals A is sum-distinct for N if A ⊆ {1,..,N} and
    the sums Σ_{a∈S} a are distinct for all subsets S ⊆ A. -/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ (Function.Injective (λ (S : Finset A) => ∑ a in S, (a : ℕ).val))

lemma IsSumDistinctSet.card_pos_of_N_pos {A : Finset ℕ} {N : ℕ}
    (h : IsSumDistinctSet A N) (hN : N ≠ 0) : 0 < A.card := by
  by_contra! h0
  have : A.card = 0 := by omega
  have hAempty : A = ∅ := Finset.card_eq_zero.mp this
  -- an empty set has only one subset sum (0)
  sorry

/-- The powerset bound: there are 2^n distinct subset sums, each in [0, N·n]. -/
lemma subset_sum_range (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    (∑ a in S, a) ≤ A.card * N := by
  calc
    (∑ a in S, a) ≤ (∑ a in S, N) := Finset.sum_le_sum (λ a ha => ?_)
    _ = S.card * N := by simp
    _ ≤ A.card * N := by
      exact Nat.mul_le_mul_right N (Finset.card_le_card (Finset.Subset.trans ?_ hA))
  sorry

/-- The minimum possible N for a given n is the function f(n) = min N such that
    ∃ A with |A| = n and A is sum-distinct for N. -/
noncomputable def min_N (n : ℕ) : ℕ :=
  sInf { N | ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = n }

lemma min_N_3 : min_N 3 = 4 := by
  -- known from OEIS A276661; A = {1, 2, 4} works
  sorry

lemma min_N_5 : min_N 5 = 13 := by
  sorry

-- EVOLVE-BLOCK-START

/-- Trivial lower bound: N ≥ (2^n - 1) / n.
    Proof: all 2^n subset sums are ≤ N·n, but they must be distinct.
    Since there are 2^n distinct nonnegative integers ≤ N·n, we have
    2^n ≤ N·n + 1, hence (2^n - 1)/n ≤ N. -/
lemma trivial_lower_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    (2 ^ A.card - 1) / A.card ≤ N := by
  sorry

/-- A constant C = 1/3 works for all n in the inequality C·2^n < N
    (using the trivial bound for all n and checking small n directly). -/
lemma constant_one_third (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    (1/3 : ℝ) * (2 : ℝ) ^ A.card < (N : ℝ) := by
  sorry

/--
Erdős-Moser bound (1956): N ≥ (1/4 - o(1)) · 2^n / √n.

This is a proven result, not open. Requires:
1. Double counting argument with Cauchy-Schwarz
2. Pairwise subset sum differences
3. Asymptotic analysis
-/
lemma erdos_moser_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    (1/4 - (1 : ℝ) / (A.card : ℝ).sqrt) * ((2 : ℝ) ^ A.card) / ((A.card : ℝ).sqrt) ≤ (N : ℝ) := by
  sorry

/--
Current best lower bound: N ≥ √(2/π) · 2^n / √n.

Proved by Elkies-Gleason (unpublished) and Dubroff-Fox-Xu (2021).
Uses the exact bound N ≥ C(n, ⌊n/2⌋).
-/
lemma best_known_lower_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    (Real.sqrt (2 / π) - (1 : ℝ) / ((A.card : ℝ).sqrt)) * ((2 : ℝ) ^ A.card) / ((A.card : ℝ).sqrt) ≤ (N : ℝ) := by
  sorry

-- EVOLVE-BLOCK-END

/-- The main open problem: does there exist C > 0 such that N > C·2^n for every
    sum-distinct set A of size n in [1,N]?

    Equivalent to: can the 1/√n factor in the lower bound be removed? -/
@[research_open]
theorem erdos_1 : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * (2 : ℝ) ^ A.card < (N : ℝ) := by
  -- EVOLVE-BLOCK-START
  sorry
  -- EVOLVE-BLOCK-END

end Erdos1
