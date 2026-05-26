import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 529

*Reference:* https://www.erdosproblems.com/529

Let $d_k(n)$ be the expected distance from the origin after taking $n$ random steps from the origin in $\mathbb{Z}^k$ (conditional on no self intersections) - that is, a self-avoiding walk. Is it true that\[\lim_{n\to \infty}\frac{d_2(n)}{n^{1/2}}= \infty?\]Is it true that\[d_k(n)\ll n^{1/2}\]for $k\geq 3$?
-/

namespace Erdos529

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos529
