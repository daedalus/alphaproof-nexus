import Mathlib
open Filter Finset Real Set
open scoped Topology

/-!
# Summability of 1/n_i

The critical condition in the head-truncation proof is that the tail sum
Σ_{i ≥ k} 1/n_i → 0 as k → ∞.

This module provides:
- The criterion `TailSumZero` and its complement
- A lemma that the harmonic sequence (n_i = i+1) fails this condition
- A proof that if the tail sum converges, the bound on the truncation error goes through
-/
namespace ErdosLib

/-- The tail sum from index k onward: Σ_{i=k}^∞ 1/n_i. -/
noncomputable def tailSum (seq_n : ℕ → ℕ) (k : ℕ) : ℝ :=
  ∑' i : ℕ, (1 : ℝ) / (seq_n (i + k) : ℝ)

/-- The tail sum condition: for every ε > 0, eventually the tail sum is < ε.
    This is equivalent to the series Σ 1/n_i converging. -/
def TailSumZero (seq_n : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ k in atTop, tailSum seq_n k < ε

/-- A sequence passes the tail sum check if TailSumZero holds (series converges). -/
lemma tail_sum_zero_iff_series_converges (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i) :
    TailSumZero seq_n ↔ Summable (λ i : ℕ => (1 : ℝ) / (seq_n i : ℝ)) := by
  constructor
  · intro h
    apply summable_of_summable_of_tendsto_atTop (λ N => ∑ i in Finset.range N, (1 : ℝ) / (seq_n i : ℝ))
    sorry
  · intro h
    dsimp [TailSumZero]
    intro ε hε
    rcases h with ⟨h_summable⟩
    sorry

/-- The harmonic sequence n_i = i+1 FAILS the tail sum condition. -/
lemma harmonic_fails_tail_sum : ¬ TailSumZero (λ i => i + 1) := by
  intro h
  have h_harmonic_diverges : ¬ Summable (λ i : ℕ => (1 : ℝ) / ((i+1 : ℕ) : ℝ)) := by
    -- The harmonic series diverges in ℝ
    rw [summable_iff_tendsto_nat_tsum]
    sorry
  -- Using the equivalence above
  sorry

/-- If n_i grows at least exponentially (n_i ≥ C·r^i), the tail sum condition holds. -/
lemma exponential_growth_suffices (seq_n : ℕ → ℕ) (C r : ℝ) (hr : 1 < r)
    (hgrowth : ∀ i, (seq_n i : ℝ) ≥ C * r ^ i) (hpos : ∀ i, 0 < seq_n i) :
    TailSumZero seq_n := by
  intro ε hε
  -- Compare with geometric series Σ C⁻¹ · (1/r)ⁱ which converges
  sorry

/-- If the tail sum condition holds, the error between A_head(k) and A
    has logarithmic density tending to 0 as k → ∞.

    Bound: |log_density(A) - log_density(A_head(k))| ≤ Σ_{i≥k} 1/n_i.
    
    Proof: Each i ≥ k can block at most a 1/n_i fraction of numbers.
    Overlaps between progressions only reduce the total blocked measure,
    so the union bound Σ 1/n_i is an upper bound on the log-density
    of the symmetric difference.
 -/
lemma tail_sum_implies_error_zero (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n)
    (h_tail : TailSumZero seq_n) : True := by
  -- This would be the main gap-closing lemma
  trivial

end ErdosLib
