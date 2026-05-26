/-
  Project Euler #23: Non-Abundant Sums
  Find the sum of all positive integers which cannot be written as the sum of two abundant numbers.
  An abundant number is one where the sum of its proper divisors exceeds itself.
  Answer: 4179871
-/
import Mathlib

namespace ProjectEuler23

def properDivisors (n : ℕ) : Finset ℕ :=
  (Nat.divisors n).filter (λ d => d ≠ n)

def abundants : Finset ℕ :=
  (Finset.Icc 1 28123).filter (λ n => (properDivisors n).sum id > n)

def abundantsList : List ℕ :=
  (Finset.sort abundants (· ≤ ·))

def memAbundants (x : ℕ) : Bool :=
  if x ∈ abundants then true else false

def isSumOfTwo (n : ℕ) : Bool :=
  abundantsList.any (λ a => (Nat.ble a n) && (memAbundants (n - a)))

def cannotBeWritten : Finset ℕ :=
  (Finset.Icc 1 28123).filter (λ n => isSumOfTwo n = false)

def result : ℕ :=
  cannotBeWritten.sum id

-- EVOLVE-BLOCK-START
theorem answer_correct : result = 4179871 := by
  native_decide
-- EVOLVE-BLOCK-END

end ProjectEuler23
