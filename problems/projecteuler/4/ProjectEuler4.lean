import Mathlib

/-!
# Project Euler Problem 4: Largest Palindrome Product

A palindromic number reads the same both ways. The largest palindrome made
from the product of two 2-digit numbers is 9009 = 91 × 99.

Find the largest palindrome made from the product of two 3-digit numbers.

Answer: 906609
-/
namespace ProjectEuler4

/-- Check whether a number is a palindrome in base 10. -/
def is_palindrome (n : ℕ) : Bool :=
  let s := n.repr
  s.toList.reverse = s.toList

/-- All products of two 3-digit numbers that are palindromes. -/
def palindrome_products : Finset ℕ :=
  (((Finset.Icc 100 999).product (Finset.Icc 100 999)).image (λ ⟨a, b⟩ => a * b)).filter
    (λ n => is_palindrome n = true)

/-- Largest palindrome product of two 3-digit numbers. -/
def largest_palindrome_product : ℕ :=
  palindrome_products.sup id

theorem answer_correct : largest_palindrome_product = 906609 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler4
