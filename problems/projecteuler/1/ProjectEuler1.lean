import Mathlib

/-!
# Project Euler Problem 1: Multiples of 3 or 5

If we list all the natural numbers below 10 that are multiples of 3 or 5,
we get 3, 5, 6 and 9. The sum of these multiples is 23.

Find the sum of all the multiples of 3 or 5 below 1000.

Answer: 233168
-/
namespace ProjectEuler1

def sum_multiples (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k => k % 3 = 0 ∨ k % 5 = 0).sum id

theorem answer_correct : sum_multiples 1000 = 233168 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler1
