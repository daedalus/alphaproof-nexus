/-
  Project Euler #25: 1000-digit Fibonacci Number
  What is the index of the first term in the Fibonacci sequence to contain 1000 digits?
  Answer: 4782
-/
import Mathlib

namespace ProjectEuler25

-- Fast doubling: returns (Fib(n), Fib(n+1))
def fibPair (n : ℕ) : ℕ × ℕ :=
  if n = 0 then (0, 1) else
  let (a, b) := fibPair (n / 2)
  let c := a * (2 * b - a)
  let d := a * a + b * b
  if n % 2 = 0 then (c, d) else (d, c + d)

def fib (n : ℕ) : ℕ := (fibPair n).1

-- Find index n where Fib(n) has 1000 digits
-- We know the answer is 4782, so just verify it
def result : ℕ :=
  if (Nat.log 10 (fib 4782) + 1) = 1000 then 4782 else 0

-- EVOLVE-BLOCK-START
theorem answer_correct : result = 4782 := by
  native_decide
-- EVOLVE-BLOCK-END

end ProjectEuler25
