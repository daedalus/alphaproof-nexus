import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 1151

*Reference:* https://www.erdosproblems.com/1151

Given $a_1,\ldots,a_n\in [-1,1]$ let\[\mathcal{L}^nf(x) = \sum_{1\leq i\leq n}f(a_i)\ell_i(x)\]be the unique polynomial of degree $n-1$ which agrees with $f$ on $a_i$ for $1\leq i\leq n$ (that is, the Lagrange interpolation polynomial).Let $a_i$ be the set of Chebyshev nodes. Prove that, for any closed $A\subseteq [-1,1]$, there exists a continuous function $f$ such that $A$ is the set of limit points of $\mathcal{L}^nf(x)$.
-/

namespace Erdos1151

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos1151
