import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 394

*Reference:* https://www.erdosproblems.com/394

Let $t_k(n)$ denote the least $m$ such that\[n\mid m(m+1)(m+2)\cdots (m+k-1).\]Is it true that\[\sum_{n\leq x}t_2(n)\ll \frac{x^2}{(\log x)^c}\]for some $c>0$?Is it true that, for $k\geq 2$,\[\sum_{n\leq x}t_{k+1}(n) =o\left(\sum_{n\leq x}t_k(n)\right)?\]
-/

namespace Erdos394

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos394
