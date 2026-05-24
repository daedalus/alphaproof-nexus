/-
  Population Member 02, Gen0: Powers of 2 upper bound.
  
  Construction: A = {1, 2, 4, ..., 2^{n-1}} ⊂ [1, 2^{n-1}] gives N = 2^{n-1}.
  Since subset sums produce all numbers from 0 to 2^n - 1 (binary representation),
  they are all distinct. This shows N = 2^{n-1} works for size n, so min_N(n) ≤ 2^{n-1}.
  
  Together with the trivial lower bound (member_01), we get:
    2^n/n < min_N(n) ≤ 2^{n-1}

  Rating (initial): Elo 1200
-/
import Mathlib
open Finset

namespace Erdos1

/-- The powers of 2 set: {2^0, 2^1, ..., 2^{k-1}} -/
def powers_of_two_set (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (λ i => 2 ^ i)

lemma card_powers_of_two_set (k : ℕ) : (powers_of_two_set k).card = k := by
  simp [powers_of_two_set]

lemma powers_of_two_set_subset_Icc (k : ℕ) : powers_of_two_set k ⊆ Finset.Icc 1 (2 ^ (k-1)) := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  have hx_pos : 1 ≤ 2 ^ i := by
    refine Nat.one_le_two_pow _
  have hx_bound : 2 ^ i ≤ 2 ^ (k-1) := by
    have hi' : i ≤ k-1 := by
      rcases Finset.mem_range.mp hi with hi_k
      omega
    exact Nat.pow_le_pow_right (by norm_num) hi'
  exact Finset.mem_Icc.mpr ⟨hx_pos, hx_bound⟩

/-- Subset sums of {1,2,4,...,2^{k-1}} produce all numbers 0..2^k-1 (binary).
    Hence they are all distinct. -/
lemma subset_sums_powers_of_two (k : ℕ) (S : Finset (powers_of_two_set k)) :
    (∑ a in S, (a : ℕ).val) < 2 ^ k := by
  -- Each element is a distinct power of 2, and the sum of distinct powers of 2 < 2^k
  sorry

/-- The powers of 2 form a sum-distinct set of size k in [1, 2^{k-1}]. -/
lemma powers_of_two_is_sum_distinct (k : ℕ) (hk : 0 < k) :
    IsSumDistinctSet (powers_of_two_set k) (2 ^ (k-1)) := by
  refine ⟨powers_of_two_set_subset_Icc k, ?_⟩
  -- Show subset sums are distinct: each subset gives a unique binary representation
  sorry

/-- Upper bound: min_N(n) ≤ 2^{n-1} for n > 0. -/
lemma upper_bound_powers_of_two (n : ℕ) (hn : 0 < n) : min_N n ≤ 2 ^ (n-1) := by
  dsimp [min_N]
  apply csInf_le (Set.nonempty_of_mem ?_)
  refine ⟨powers_of_two_set n, powers_of_two_is_sum_distinct n hn, ?_⟩
  simp [card_powers_of_two_set]

end Erdos1
