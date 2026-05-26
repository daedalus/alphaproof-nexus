import Mathlib

/-!
# Project Euler Problem 9: Special Pythagorean Triplet

A Pythagorean triplet is a set of three natural numbers, a < b < c, for which
a² + b² = c².

For example, 3² + 4² = 9 + 16 = 25 = 5².

There exists exactly one Pythagorean triplet for which a + b + c = 1000.
Find the product abc.

Answer: 31875000
-/
namespace ProjectEuler9

theorem answer_correct : ∃ a b c : ℕ, a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a + b + c = 1000 ∧ a * b * c = 31875000 := by
  -- EVOLVE-BLOCK-START
  refine ⟨200, 375, 425, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  -- EVOLVE-BLOCK-END

end ProjectEuler9
