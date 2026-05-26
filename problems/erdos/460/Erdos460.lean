import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 460

*Reference:* https://www.erdosproblems.com/460

Let $a_0=0$ and $a_1=1$, and in general define $a_k$ to be the least integer $>a_{k-1}$ for which $(n-a_k,n-a_i)=1$ for all $0\leq i<k$. Does\[\sum_{0<a_i< n}\frac{1}{a_i}\to \infty\]as $n\to \infty$? What about if we restrict the sum to those $i$ such that $n-a_j$ is divisible by some prime $\leq a_j$, or the complement of such $i$?
-/

namespace Erdos460

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos460
