import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 430

*Reference:* https://www.erdosproblems.com/430

Fix some integer $n$ and define a decreasing sequence in $[1,n)$ by $a_1=n-1$ and, for $k\geq 2$, letting $a_k$ be the greatest integer in $[1,a_{k-1})$ such that all of the prime factors of $a_k$ are $>n-a_k$.Is it true that, for sufficiently large $n$, not all of this sequence can be prime?
-/

namespace Erdos430

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos430
