/-
  Project Euler #24: Lexicographic Permutations
  What is the millionth lexicographic permutation of the digits 0, 1, 2, 3, 4, 5, 6, 7, 8, 9?
  Answer: 2783915460
-/
import Mathlib

namespace ProjectEuler24

def factorial (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod id

def _get? : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n+1 => _get? as n

def factoradic (n : ℕ) : List ℕ :=
  let rec go (k : ℕ) (remaining : ℕ) : List ℕ :=
    if h : k = 0 then []
    else
      let f := factorial (k - 1)
      let digit := remaining / f
      digit :: go (k - 1) (remaining % f)
  go 10 n

def permute (digits : List ℕ) (fac : List ℕ) : List ℕ :=
  match digits, fac with
  | [], _ => []
  | _, [] => []
  | ds, c :: cs =>
    let idx := c
    let selected := (_get? ds idx).getD 0
    let rest := ds.erase selected
    selected :: permute rest cs

def result : ℕ :=
  let digits := [0,1,2,3,4,5,6,7,8,9]
  let fac := factoradic 999999
  let perm := permute digits fac
  perm.foldl (λ acc d => acc * 10 + d) 0

-- EVOLVE-BLOCK-START
theorem answer_correct : result = 2783915460 := by
  native_decide
-- EVOLVE-BLOCK-END

end ProjectEuler24
