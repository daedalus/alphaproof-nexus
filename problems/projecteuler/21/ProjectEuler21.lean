/-
  Project Euler #21: Amicable Numbers
  Let d(n) be the sum of proper divisors of n.
  Evaluate the sum of all amicable numbers under 10000.
  Answer: 31626
-/
import Mathlib

namespace ProjectEuler21

def properDivisors (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter (λ d => d ≠ n)

def d (n : ℕ) : ℕ :=
  (properDivisors n).sum id

def amicableNumbers : Finset ℕ :=
  (Finset.Icc 1 9999).filter (λ n =>
    let dn := d n
    dn ≠ n ∧ d dn = n)

def amicableSum : ℕ :=
  amicableNumbers.sum id

-- EVOLVE-BLOCK-START
theorem answer_correct : amicableSum = 31626 := by
  native_decide
-- EVOLVE-BLOCK-END

end ProjectEuler21
