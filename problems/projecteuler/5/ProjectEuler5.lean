import Mathlib

/-!
# Project Euler Problem 5: Smallest Multiple

2520 is the smallest number that can be divided by each of the numbers from 1
to 10 without any remainder.

What is the smallest positive number that is evenly divisible by all of the
numbers from 1 to 20?

Answer: 232792560
-/
namespace ProjectEuler5

/-- Compute lcm of all numbers from 1 to n. -/
def lcm_up_to (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

theorem answer_correct : lcm_up_to 20 = 232792560 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler5
