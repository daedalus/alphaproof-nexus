/-
  Project Euler #28: Number Spiral Diagonals
  What is the sum of the numbers on the diagonals in a 1001 by 1001 spiral?
  Answer: 669171001
-/
import Mathlib

namespace ProjectEuler28

-- For a 1001×1001 spiral, corners of ring k (1-indexed):
-- top-right: (2k+1)², top-left: (2k+1)² - 2k, bottom-left: (2k+1)² - 4k, bottom-right: (2k+1)² - 6k
-- Sum of corners for ring k: 4*(2k+1)² - 12k = 16k² + 4k + 4
-- Sum over k=1..500, plus center (1)

def ringCornerSum (k : ℕ) : ℕ :=
  16 * k ^ 2 + 4 * k + 4

def spiralDiagSum : ℕ :=
  1 + (Finset.Icc 1 500).sum ringCornerSum

-- EVOLVE-BLOCK-START
theorem answer_correct : spiralDiagSum = 669171001 := by
  native_decide
-- EVOLVE-BLOCK-END

end ProjectEuler28
