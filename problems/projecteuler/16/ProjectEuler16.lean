import Mathlib

/-!
# Project Euler Problem 16: Power Digit Sum

2^15 = 32768 and the sum of its digits is 3 + 2 + 7 + 6 + 8 = 26.

What is the sum of the digits of the number 2^1000?

Answer: 1366
-/
namespace ProjectEuler16

def digit_sum (n : ℕ) : ℕ :=
  (Nat.digits 10 n).sum

theorem answer_correct : digit_sum (2 ^ 1000) = 1366 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler16
