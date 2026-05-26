import Mathlib

/-!
# Project Euler Problem 17: Number Letter Counts

If the numbers 1 to 5 are written out in words: one, two, three, four, five,
then there are 3 + 3 + 5 + 4 + 4 = 19 letters used in total.

If all the numbers from 1 to 1000 (one thousand) inclusive were written out in
words, how many letters would be used?

Answer: 21124
-/
namespace ProjectEuler17

/-- Number of letters in the English word for numbers 1..1000 (excluding spaces/hyphens). -/
def letter_count (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n ≤ 19 then
    match n with
    | 1 => 3 | 2 => 3 | 3 => 5 | 4 => 4 | 5 => 4
    | 6 => 3 | 7 => 5 | 8 => 5 | 9 => 4 | 10 => 3
    | 11 => 6 | 12 => 6 | 13 => 8 | 14 => 8 | 15 => 7
    | 16 => 7 | 17 => 9 | 18 => 8 | 19 => 8
    | _ => 0
  else if n < 100 then
    let tens := n / 10
    let ones := n % 10
    (match tens with
    | 2 => 6 | 3 => 6 | 4 => 5 | 5 => 5
    | 6 => 5 | 7 => 7 | 8 => 6 | 9 => 6
    | _ => 0) + letter_count ones
  else if n < 1000 then
    let hundreds := n / 100
    let rest := n % 100
    letter_count hundreds + 7 + (if rest = 0 then 0 else 3 + letter_count rest)
  else if n = 1000 then 11
  else 0

def total_letters_up_to_1000 : ℕ :=
  (Finset.Icc 1 1000).sum letter_count

theorem answer_correct : total_letters_up_to_1000 = 21124 := by
  -- EVOLVE-BLOCK-START
  native_decide
  -- EVOLVE-BLOCK-END

end ProjectEuler17
