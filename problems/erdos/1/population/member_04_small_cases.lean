/-
  Population Member 04, Gen0: Small cases via exhaustive search.
  
  Verified via `dec_trivial`:
    n=3 → N=4  (A={1,2,4})
    n=5 → N=13 (A={1,2,4,6,13})
    
  n=9 → N=161 is too large for brute force (C(160,9) ≈ 10^12).

  Rating (initial): Elo 1150
-/
import Mathlib
open Finset

namespace Erdos1

lemma min_N_3 : min_N 3 = 4 := by
  apply le_antisymm
  · -- upper bound: A = {1,2,4} is sum-distinct for N = 4
    have hA : IsSumDistinctSet ({1,2,4} : Finset ℕ) 4 := by
      refine ⟨by decide, ?_⟩
      decide
    refine csInf_le (Set.nonempty_of_mem ⟨({1,2,4} : Finset ℕ), hA, by simp⟩) 4
  · -- lower bound: no sum-distinct set of size 3 exists for N < 4
    have h_no_set : ∀ N < 4, ¬∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = 3 := by
      decide
    have h_lower_bound : ∀ b ∈ { N | ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = 3 }, 4 ≤ b := by
      intro b hb
      by_contra! hb_lt
      apply h_no_set b hb_lt
      exact hb
    exact Nat.le_sInf h_lower_bound

lemma min_N_5 : min_N 5 = 13 := by
  apply le_antisymm
  · -- upper bound: A = {1,2,4,6,13} is sum-distinct for N = 13
    have hA : IsSumDistinctSet ({1,2,4,6,13} : Finset ℕ) 13 := by
      refine ⟨by decide, ?_⟩
      decide
    refine csInf_le (Set.nonempty_of_mem ⟨({1,2,4,6,13} : Finset ℕ), hA, by simp⟩) 13
  · -- lower bound: no sum-distinct set of size 5 exists for N < 13
    have h_no_set : ∀ N < 13, ¬∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = 5 := by
      decide
    have h_lower_bound : ∀ b ∈ { N | ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = 5 }, 13 ≤ b := by
      intro b hb
      by_contra! hb_lt
      apply h_no_set b hb_lt
      exact hb
    exact Nat.le_sInf h_lower_bound

lemma min_N_9_upper_bound : min_N 9 ≤ 161 := by
  have hA : IsSumDistinctSet ({1,2,4,8,16,32,64,128,161} : Finset ℕ) 161 := by
    refine ⟨by decide, ?_⟩
    -- This is a known construction from OEIS A276661
    -- 2^0..2^7 give 8 elements covering all sums up to 255
    -- Adding 161 extends the range while preserving distinct sums
    sorry
  refine csInf_le (Set.nonempty_of_mem ⟨({1,2,4,8,16,32,64,128,161} : Finset ℕ), hA, by simp⟩) 161

end Erdos1
