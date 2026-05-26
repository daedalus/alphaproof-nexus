import Mathlib

/-!
# Project Euler Problem 15: Lattice Paths

Starting in the top left corner of a 2×2 grid, and only being able to move to
the right and down, there are exactly 6 routes to the bottom right corner.

How many such routes are there through a 20×20 grid?

Answer: 137846528820
-/
namespace ProjectEuler15

/-- Number of lattice paths from (0,0) to (a,b) moving only right and down.
    This is C(a+b, a). -/
def lattice_paths (a b : ℕ) : ℕ :=
  Nat.choose (a + b) a

theorem answer_correct : lattice_paths 20 20 = 137846528820 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler15
