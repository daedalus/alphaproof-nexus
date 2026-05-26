/-
  Population Member 03, Gen0: Main open problem — existence of a constant.
  
  Goal: prove ∃ C > 0 such that N > C·2^n for all sum-distinct sets.
  
  Strategy: improve the trivial bound using:
  1. Cauchy-Schwarz on subset sum differences (Erdős-Moser technique)
  2. Fourier analysis / characters on the subset sum distribution
  3. Probabilistic method: random A has sum collisions with probability
     that depends on N/n·2^n ratio
  
  The key inequality to beat: 2^n ≤ N·n + 1 (trivial)
  We need: C·2^n < N for some C > 0, i.e., 2^n = O(N).
  
  Currently stuck because the trivial bound only gives 2^n = O(N·n),
  and removing the n factor seems to require new ideas.

  Rating (initial): Elo 1250
-/
import Mathlib
open Finset
open Real
open scoped BigOperators

namespace Erdos1

/-- The open core: can we show that min_N(n)/2^n is bounded away from 0? -/
lemma main_conjecture_asymptotic : Filter.Tendsto (λ n => (min_N n : ℝ) / (2 : ℝ) ^ n) Filter.atTop (𝓝 (∞ : ℝ)) := by
  sorry

/-- The weak form: there exists SOME positive constant C. -/
lemma main_conjecture_weak : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * (2 : ℝ) ^ A.card < (N : ℝ) := by
  -- Approach: try to prove by contradiction using the trivial bound plus additional constraints
  by_contra! h
  -- h: ∀ C > 0, ∃ N A, IsSumDistinctSet A N ∧ N ≠ 0 ∧ C·2^{|A|} ≥ N
  -- This means we can find sum-distinct sets with N arbitrarily small relative to 2^n
  -- Contradict the trivial bound? No, the trivial bound allows N as small as 2^n/n.
  -- So a new idea is needed.
  sorry

/-- Freiman's theorem / Plünnecke-Ruzsa approach.
    If N is small relative to 2^n, the subset sum set Σ(A) = {Σ_{a∈S} a | S⊆A}
    has small doubling. By sumset estimates, A must have additive structure.
    The distinct subset sums constraint might then force N to be large.
    
    Specifically: Σ(A) = sumset of A (over all subsets).
    If |A| = n and max(A) = N, then Σ(A) ⊆ [0, nN].
    Distinctness implies |Σ(A)| = 2^n.
    If N < C·2^n, then Σ(A) ⊆ [0, n·C·2^n], so |Σ(A)| ≤ n·C·2^n + 1.
    Since |Σ(A)| = 2^n, we get 2^n ≤ n·C·2^n + 1, so 1 ≤ n·C for large n.
    This gives C ≥ 1/n, which goes to 0.
    
    The gap: can we do better using the structure of Σ(A)?
    Σ(A) = A ⊕ A ⊕ ... ⊕ A (n-fold sumset with 0/1 coefficients).
    If Σ(A) is small, A must be arithmetic.
    An arithmetic A would mean Σ(A) has gaps that could limit its size.
    But powers of 2 are NOT arithmetic, yet they give N small.
    This suggests the conjecture is about ruling out the powers-of-2 structure
    for very small N. -/
lemma plunnecke_ruzza_approach : False := by
  sorry

/--
  Another approach: use the fact that the subset sums are also all distinct modulo m.
  Choose m ≈ 2^n/N. By pigeonhole principle, some residue class has many subset sums.
  Then differences of subset sums in the same class give...
  
  This is the starting point of the Erdős-Moser proof (which gives 2^n/√n).
  Can the exponent be improved?
-/
lemma modular_approach (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    ∃ C > 0, C * (2 : ℝ) ^ A.card < (N : ℝ) := by
  sorry

end Erdos1
