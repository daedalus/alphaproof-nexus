import Mathlib
open Finset

/-!
# Erdős Problem 1: Sum-Distinct Sets

**Reference:** [erdosproblems.com/1](https://www.erdosproblems.com/1)

If $A \subseteq \{1, \ldots, N\}$ with $|A| = n$ is such that the subset sums
$\sum_{a \in S} a$ are distinct for all $S \subseteq A$ then $N \gg 2^n$.

Open, $500. Tags: number theory, additive combinatorics.

## Known results
- Trivial: $N \gg 2^n / n$ (counting)
- Erdős–Moser (1956): $N \geq (1/4 - o(1)) \cdot 2^n / \sqrt{n}$
- Current best: $N \geq \sqrt{2/\pi} \cdot 2^n / \sqrt{n}$
- Upper bound (Bohman): $N \leq 0.22002 \cdot 2^n$
- Small cases (OEIS A276661): n=3→N=4, n=5→N=13, n=9→N=161
-/
namespace Erdos1

/-- A ⊆ {1..N} with all subset sums distinct. -/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ (Function.Injective (λ (S : Finset A) => ∑ a in S, (a : ℕ).val))

/-- min_N(n) = smallest N allowing a sum-distinct set of size n. -/
noncomputable def min_N (n : ℕ) : ℕ :=
  sInf { N | ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = n }

/-- The main open problem: does there exist C > 0 such that N > C·2^n for every
    sum-distinct set A of size n in [1,N]? Equivalent to: can the 1/√n factor
    in the current best bound be removed? -/
@[research_open]
theorem erdos_1 : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * (2 : ℝ) ^ A.card < (N : ℝ) := by
  -- EVOLVE-BLOCK-START
  sorry
  -- EVOLVE-BLOCK-END

end Erdos1
