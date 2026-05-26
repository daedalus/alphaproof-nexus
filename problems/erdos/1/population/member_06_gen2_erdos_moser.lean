/-
  Population Member 06 (Gen 2): Erdős-Moser via cross-correlation bound

  Strategy: Replace the pigeonhole bound 2^n ≤ n·N + 1 with a tighter
  bound using the fact that subset sums have small *variance*.

  Key idea: Let σ_1 < ... < σ_{2^n} be the sorted subset sums.
  Define the *gaps* g_i = σ_{i+1} - σ_i ≥ 1.
  By Cauchy-Schwarz: (∑ g_i)(∑ 1/g_i) ≥ (2^n - 1)^2.
  Since ∑ g_i = σ_{2^n} - σ_1 ≤ n·N, we have ∑ 1/g_i ≥ (2^n - 1)^2/(n·N).

  New approach: Show ∑ 1/g_i ≤ C·n·2^n/(N²) using a second-moment
  (cross-correlation) estimate on the subset sum distribution. Then
  combining gives (2^n - 1)^2/(n·N) ≤ C·n·2^n/(N²) ⇒ N ≥ C'·2^n/(n²).

  This requires: (1) bounding the overlap of subset sums via
  collision counting, (2) applying Chebyshev to the gap distribution.

  Rating (initial): Elo 1250
-/

import Mathlib
open Finset
open Real
open scoped BigOperators

namespace Erdos1

/-- The gaps between consecutive sorted subset sums. -/
def gaps (A : Finset ℕ) : Finset ℕ :=
  let sums := (Finset.image (λ S : Finset A => ∑ a in S, (a : ℕ).val) Finset.univ).sort (· ≤ ·)
  Finset.image (λ i => if hi : i+1 < sums.length then sums.get (i+1) - sums.get i else 0) (Finset.range (2^A.card - 1))

/-- The sum of the gaps equals the range of the subset sums. -/
lemma sum_gaps_eq_range (A : Finset ℕ) (hA : A.Nonempty) : (∑ g in gaps A, g) = (Finset.max' (subset_sums A) ?_) - (Finset.min' (subset_sums A) ?_) := by
  sorry

/-- The pigeonhole bound for nonempty A. -/
lemma trivial_bound_nonempty (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hA : A.Nonempty) (hN : N ≠ 0) :
    (2 ^ A.card - 1) / A.card ≤ N := by
  exact trivial_bound A N h hN

/-- The number of distinct values of |∑(S)-∑(T)| among S,T subsets of A.
    By Cauchy-Schwarz, this is bounded below by (2^n-1)²/(n·N). -/
lemma gap_cauchy_schwarz_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    (2 ^ A.card - 1)^2 / (A.card * N) ≤ ∑ g in gaps A, 1 / (g : ℝ) := by
  sorry

/-- Upper bound on ∑ 1/g via second-moment cross-correlation.
    Each gap g_i is at least 1, but many gaps must be large because
    the subset sums are confined to [0, n·N]. -/
lemma gap_second_moment_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    ∑ g in gaps A, (1 : ℝ) / (g : ℝ) ≤ (2 ^ A.card : ℝ)^2 / (N : ℝ) := by
  sorry

/-- Combining the two bounds: (2^n-1)^2/(n·N) ≤ 2^(2n)/N.
    Rearranging: N ≥ (2^n-1)^2/(n·2^(2n)) ≈ 2^n / (n·4^n).
    This is much weaker than the trivial bound! This approach needs refinement. -/
lemma combined_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) (hA : A.Nonempty) :
    (2 ^ (2 * A.card) : ℝ) / (A.card : ℝ) ≤ (N : ℝ) := by
  sorry

-- EVOLVE-BLOCK-START

/-- Improved bound: there exists C > 0 such that N > C·2^n / n.
    This improves the trivial bound (2^n - 1)/n ≤ N by a constant factor.
    Uses the Erdős-Moser multi-selection technique. -/
lemma improved_bound_exists_C : ∃ (C : ℝ), C > 0 ∧ ∀ (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0),
    C * ((2 : ℝ) ^ A.card) / (A.card : ℝ) ≤ (N : ℝ) := by
  sorry

-- EVOLVE-BLOCK-END

end Erdos1
