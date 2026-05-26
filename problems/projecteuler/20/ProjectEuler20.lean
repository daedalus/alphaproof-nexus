import Mathlib

/-!
# Project Euler Problem 20: Factorial Digit Sum

n! means n × (n − 1) × ... × 3 × 2 × 1.

For example, 10! = 10 × 9 × ... × 3 × 2 × 1 = 3628800,
and the sum of the digits in the number 10! is 3 + 6 + 2 + 8 + 8 + 0 + 0 = 27.

Find the sum of the digits in the number 100!

Answer: 648
-/
namespace ProjectEuler20

def factorial (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod id

def digit_sum (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum

theorem answer_correct : digit_sum (factorial 100) = 648 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler20
