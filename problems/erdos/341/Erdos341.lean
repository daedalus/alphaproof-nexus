import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 341

*Reference:* https://www.erdosproblems.com/341

Let $A=\{a_1<\cdots<a_k\}$ be a finite set of positive integers and extend it to an infinite sequence $\overline{A}=\{a_1<a_2<\cdots \}$ by defining $a_{n+1}$ for $n\geq k$ to be the least integer exceeding $a_n$ which is not of the form $a_i+a_j$ with $i,j\leq n$. Is it true that the sequence of differences $a_{m+1}-a_m$ is eventually periodic?
-/

namespace Erdos341

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos341
