import Mathlib

/-!
# Project Euler Problem 3: Largest Prime Factor

The prime factors of 13195 are 5, 7, 13 and 29.

What is the largest prime factor of the number 600851475143?

Answer: 6857
-/
namespace ProjectEuler3

/-- The largest prime factor of n (returns 0 if n ≤ 1). -/
def largest_prime_factor (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter fun p => p ∣ n ∧ Nat.Prime p).sup id

theorem answer_correct : largest_prime_factor 600851475143 = 6857 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler3
