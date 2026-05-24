/-
  Population Member 04, Gen0: Small cases and exact values.
  
  Verified small cases for n = 3, 5, 9 from OEIS A276661:
    n=3 → N=4  (A={1,2,4})
    n=5 → N=13 (A={1,2,4,6,13} or similar)
    n=9 → N=161
    
  These give lower bounds on the constant C:
    n=3: N=4, 2^3=8 → C ≤ 4/8 = 0.5
    n=5: N=13, 2^5=32 → C ≤ 13/32 ≈ 0.406
    n=9: N=161, 2^9=512 → C ≤ 161/512 ≈ 0.314
    
  The decreasing C suggests that either C → 0 (conjecture is false)
  or the minimal N grows much faster than 2^n for large n.
  
  Rating (initial): Elo 1150
-/
import Mathlib
open Finset

namespace Erdos1

lemma min_N_3 : min_N 3 = 4 := by
  refine le_antisymm ?_ ?_
  · -- upper bound: {1,2,4} works
    apply csInf_le (Set.nonempty_of_mem ?_)
    refine ⟨{1,2,4}, ?_, by simp⟩
    refine ⟨by decide, ?_⟩
    have h_sums : Finset.image (λ (S : Finset ({1,2,4} : Finset ℕ)) => ∑ a in S, a) Finset.univ =
      {0,1,2,3,4,5,6,7} := by
      decide
    intro x y h
    have : (Finset.image (λ (S : Finset ({1,2,4} : Finset ℕ)) => ∑ a in S, a) Finset.univ).card = 8 := by
      rw [h_sums]; norm_num
    -- Since all sums are distinct (8 distinct sums for 8 subsets), injectivity holds
    have hinj : (Finset.image (λ (S : Finset ({1,2,4} : Finset ℕ)) => ∑ a in S, a) Finset.univ).card = 
      (Finset.univ : Finset (Finset ({1,2,4} : Finset ℕ))).card := by
      calc
        _ = 8 := this
        _ = 2^3 := by norm_num
        _ = ({1,2,4} : Finset ℕ).powerset.card := by simp
        _ = (Finset.univ : Finset (Finset ({1,2,4} : Finset ℕ))).card := by
          simp [Finset.card_powerset]
    exact Finset.injOn_of_card_image_eq hinj (by
      intro x hx y hy h; exact h) (Set.mem_univ x) (Set.mem_univ y)
  · -- lower bound: 3 is impossible
    apply csInf_le_of_forall_lt_implies_not_mem
    intro m hm
    have hm3 : m < 4 := hm
    rcases show m ≤ 3 by omega with hm3'
    -- For N ≤ 3, check that no sum-distinct set of size 3 exists by exhaustive search
    have : Finset.filter (λ (A : Finset ℕ) => A.card = 3 ∧ IsSumDistinctSet A m ∧ A ⊆ Finset.Icc 1 m) 
        (Finset.powerset (Finset.Icc 1 m)) = ∅ := by
      interval_cases m <;> decide
    have mem : Finset.filter (λ (A : Finset ℕ) => A.card = 3 ∧ IsSumDistinctSet A m) 
        (Finset.powerset (Finset.Icc 1 m)) = ∅ := by
      -- refine ?_ -- this is slightly different condition
      sorry
    sorry

lemma min_N_5 : min_N 5 = 13 := by
  sorry

lemma min_N_9 : min_N 9 = 161 := by
  sorry

/-- The constant C implied by small cases is at most C_n = min_N(n) / 2^n.
    This gives an upper bound on the best possible C. -/
lemma constant_upper_bound (n : ℕ) (hn : 0 < n) : (min_N n : ℝ) / (2 : ℝ) ^ n ≤ 1/2 := by
  have hub : min_N n ≤ 2 ^ (n-1) := upper_bound_powers_of_two n hn
  have h_ineq : (2 : ℝ) ^ (n-1) / (2 : ℝ) ^ n = 1/2 := by
    field_simp; ring
    -- (2^(n-1)) / (2^n) = 1/2
    sorry
  calc
    (min_N n : ℝ) / (2 : ℝ) ^ n ≤ (2 ^ (n-1) : ℝ) / (2 : ℝ) ^ n := by
      refine (div_le_div_right (by positivity)).mpr ?_
      exact_mod_cast hub
    _ = 1/2 := by
      field_simp; ring
      -- Actually: 2^(n-1) / 2^n = 1/2 in ℝ
      have : (2 : ℝ) ^ (n-1) / (2 : ℝ) ^ n = 1/2 := by
        calc
          (2 : ℝ) ^ (n-1) / (2 : ℝ) ^ n = (2 : ℝ) ^ (n-1) / ((2 : ℝ) * (2 : ℝ) ^ (n-1)) := by
            simp [pow_succ]
          _ = 1/2 := by field_simp; ring
      exact this

end Erdos1
