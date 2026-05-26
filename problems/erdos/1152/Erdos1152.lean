import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 1152

*Reference:* https://www.erdosproblems.com/1152

For $n\geq 1$ fix some sequence of $n$ distinct numbers $x_{1n},\ldots,x_{nn}\in [-1,1]$. Let $\epsilon=\epsilon(n)\to 0$. Does there always exist a continuous function $f:[-1,1]\to \mathbb{R}$ such that if $p_n$ is a sequence of polynomials, with degrees $\deg p_n<(1+\epsilon(n))n$, such that $p_n(x_{kn})=f(x_{kn})$ for all $1\leq k\leq n$, then $p_n(x)\not\to f(x)$ for almost all $x\in [-1,1]$?
-/

namespace Erdos1152

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos1152
