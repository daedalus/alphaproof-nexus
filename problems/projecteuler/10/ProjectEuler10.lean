import Mathlib

/-!
# Project Euler Problem 10: Summation of Primes

The sum of the primes below 10 is 2 + 3 + 5 + 7 = 17.

Find the sum of all the primes below two million.

Answer: 142913828922
-/
namespace ProjectEuler10

def sum_primes_below (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).sum id

theorem answer_correct : sum_primes_below 2000000 = 142913828922 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler10
