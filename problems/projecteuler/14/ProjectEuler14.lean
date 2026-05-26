import Mathlib

/-!
# Project Euler Problem 14: Longest Collatz Sequence

The following iterative sequence is defined for the set of positive integers:

n → n/2 (n even)
n → 3n + 1 (n odd)

Which starting number under one million produces the longest chain?

Answer: 837799
-/
namespace ProjectEuler14

/-- Collatz chain length bounded by fuel (structurally decreasing on fuel). -/
def collatz_len (n fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    if n ≤ 1 then 1
    else if n % 2 = 0 then 1 + collatz_len (n / 2) fuel'
    else 1 + collatz_len (3 * n + 1) fuel'

/-- The Collatz length of n (fuel = 1000 is enough for n < 1 million). -/
def collatz_length (n : ℕ) : ℕ :=
  collatz_len n 1000

theorem answer_correct :
    collatz_length 837799 = 525 ∧
    (∀ n, n ∈ Finset.Icc 1 999999 → collatz_length n ≤ collatz_length 837799) := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler14
