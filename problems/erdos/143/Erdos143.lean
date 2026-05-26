import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 143

*Reference:* https://www.erdosproblems.com/143

Let $A\subset (1,\infty)$ be a countably infinite set such that for all $x\neq y\in A$ and integers $k\geq 1$ we have\[ \lvert kx -y\rvert \geq 1.\]Does this imply that $A$ is sparse? In particular, does this imply that\[\sum_{x\in A}\frac{1}{x\log x}<\infty\]or\[\sum_{\substack{x <n\\ x\in A}}\frac{1}{x}=o(\log n)?\]
-/

namespace Erdos143

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos143
