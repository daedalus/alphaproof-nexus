import Mathlib

/-!
# Project Euler Problem 6: Sum Square Difference

The sum of the squares of the first ten natural numbers is,
1² + 2² + ... + 10² = 385.

The square of the sum of the first ten natural numbers is,
(1 + 2 + ... + 10)² = 55² = 3025.

Hence the difference between the sum of the squares of the first ten natural
numbers and the square of the sum is 3025 − 385 = 2640.

Find the difference between the sum of the squares of the first one hundred
natural numbers and the square of the sum.

Answer: 25164150
-/
namespace ProjectEuler6

def sum_square_diff (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).sum id) ^ 2 - ((Finset.Icc 1 n).sum (λ k => k ^ 2))

theorem answer_correct : sum_square_diff 100 = 25164150 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler6
