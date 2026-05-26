import Mathlib

/-!
# Project Euler Problem 7: 10001st Prime

By listing the first six prime numbers: 2, 3, 5, 7, 11, and 13, we can see
that the 6th prime is 13.

What is the 10,001st prime number?

Answer: 104743
-/
namespace ProjectEuler7

def primes_upto_200000 : List ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 200000)).sort (· ≤ ·)

-- The 10001st prime (1-indexed).
def answer : ℕ :=
  primes_upto_200000.get ⟨10000, by native_decide⟩

theorem answer_correct : answer = 104743 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler7
