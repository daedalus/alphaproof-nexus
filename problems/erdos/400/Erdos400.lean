import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 400

*Reference:* https://www.erdosproblems.com/400

For any $k\geq 2$ let $g_k(n)$ denote the maximum value of\[(a_1+\cdots+a_k)-n\]where $a_1,\ldots,a_k$ are integers such that $a_1!\cdots a_k! \mid n!$. Can one show that\[\sum_{n\leq x}g_k(n) \sim c_k x\log x\]for some constant $c_k$? Is it true that there is a constant $c_k$ such that for almost all $n<x$ we have\[g_k(n)=c_k\log x+o(\log x)?\]
-/

namespace Erdos400

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos400
