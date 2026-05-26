import Mathlib

/-!
# Project Euler Problem 18: Maximum Path Sum I

By starting at the top of the triangle below and moving to adjacent numbers
on the row below, the maximum total from top to bottom is 23.

   3
  7 4
 2 4 6
8 5 9 3

That is, 3 + 7 + 4 + 9 = 23.

Find the maximum total from top to bottom of the 15-row triangle.

Answer: 1074
-/
namespace ProjectEuler18

/-- Triangle stored as a flat list (row 0, then row 1, etc.). -/
def flat : List ℕ := [
  75,
  95, 64,
  17, 47, 82,
  18, 35, 87, 10,
  20,  4, 82, 47, 65,
  19,  1, 23, 75,  3, 34,
  88,  2, 77, 73,  7, 63, 67,
  99, 65,  4, 28,  6, 16, 70, 92,
  41, 41, 26, 56, 83, 40, 80, 70, 33,
  41, 48, 72, 33, 47, 32, 37, 16, 94, 29,
  53, 71, 44, 65, 25, 43, 91, 52, 97, 51, 14,
  70, 11, 33, 28, 77, 73, 17, 78, 39, 68, 17, 57,
  91, 71, 52, 38, 17, 14, 91, 43, 58, 50, 27, 29, 48,
  63, 66,  4, 68, 89, 53, 67, 30, 73, 16, 69, 87, 40, 31,
   4, 62, 98, 27, 23,  9, 70, 98, 73, 93, 38, 53, 60,  4, 23
]

/-- Safe list index. -/
def safe_get (l : List ℕ) (i : ℕ) : ℕ :=
  if h : i < l.length then l.get ⟨i, h⟩ else 0

/-- Index into triangle: row r, col c (0-indexed). -/
def idx (r c : ℕ) : ℕ :=
  r * (r + 1) / 2 + c

/-- Value at (r,c). -/
def val_at (r c : ℕ) : ℕ :=
  safe_get flat (idx r c)

/-- Sum along a path determined by bitmask (0..2^14-1);
    bit k decides left(0) or right(1) movement at step k. -/
def path_sum (mask : ℕ) : ℕ :=
  (Finset.range 15).sum (λ r =>
    val_at r (((Finset.range r).filter (λ k => ((mask / 2 ^ k) % 2 = 1))).card))

/-- All path sums. -/
def all_sums : Finset ℕ :=
  (Finset.range (2 ^ 14)).image path_sum

/-- Maximum path sum. -/
def max_sum : ℕ :=
  all_sums.sup id

theorem answer_correct : max_sum = 1074 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler18
