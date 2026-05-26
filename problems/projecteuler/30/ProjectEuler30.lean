/-
  Project Euler #30: Digit Fifth Powers
  Find the sum of all numbers that can be written as the sum of fifth powers of their digits.
  Answer: 443839
-/
import Mathlib

namespace ProjectEuler30

-- Upper bound: 9⁵ × 6 = 354294 (7-digit numbers can't equal sum of 5th powers of digits)
def upperBound : ℕ := 354294

def digitFifthPowerSum (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).map (λ d => d ^ 5)).sum

def matchingNumbers : Finset ℕ :=
  (Finset.Icc 2 upperBound).filter (λ n => n = digitFifthPowerSum n)

def result : ℕ :=
  matchingNumbers.sum id

-- EVOLVE-BLOCK-START
theorem answer_correct : result = 443839 := by
  native_decide
-- EVOLVE-BLOCK-END

end ProjectEuler30
