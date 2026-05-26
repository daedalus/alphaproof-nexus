/-
  Project Euler #26: Reciprocal Cycles
  Find the value of d < 1000 for which 1/d contains the longest recurring cycle in its decimal fraction part.
  Answer: 983
-/
import Mathlib

namespace ProjectEuler26

def cycleLength (d : ℕ) : ℕ :=
  if d ≤ 1 ∨ d % 2 = 0 ∨ d % 5 = 0 then 0 else
  go d 1 0
where
  go (fuel : ℕ) (r : ℕ) (k : ℕ) : ℕ :=
    match fuel with
    | 0 => 0
    | fuel'+1 =>
      let r' := (r * 10) % d
      if r' = 1 then k + 1
      else go fuel' r' (k + 1)

def result : ℕ :=
  go 1 1 0
where
  go (d best bestLen : ℕ) : ℕ :=
    if d ≥ 1000 then best
    else
      let len := cycleLength d
      if len > bestLen then go (d + 1) d len
      else go (d + 1) best bestLen

-- EVOLVE-BLOCK-START
theorem answer_correct : result = 983 := by
  native_decide
-- EVOLVE-BLOCK-END

end ProjectEuler26
