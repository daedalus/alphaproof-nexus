import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 626

*Reference:* https://www.erdosproblems.com/626

Let $k\geq 4$ and $g_k(n)$ denote the largest $m$ such that there is a graph on $n$ vertices with chromatic number $k$ and girth $>m$ (i.e. contains no cycle of length $\leq m$). Does\[\lim_{n\to \infty}\frac{g_k(n)}{\log n}\]exist?Conversely, if $h^{(m)}(n)$ is the maximal chromatic number of a graph on $n$ vertices with girth $>m$ then does\[\lim_{n\to \infty}\frac{\log h^{(m)}(n)}{\log n}\]exist, and what is its value?
-/

namespace Erdos626

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos626
