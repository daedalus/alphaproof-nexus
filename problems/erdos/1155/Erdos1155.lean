import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 1155

*Reference:* https://www.erdosproblems.com/1155

Construct a random graph on $n$ vertices in the following way: begin with the complete graph $K_n$. At each stage, choose uniformly a random triangle in the graph and delete all the edges of this triangle. Repeat until the graph is triangle-free.Describe the typical parameters and structure of such a graph. In particular, if $f(n)$ is the number of edges remaining, then is it true that\[\mathbb{E}f(n)\asymp n^{3/2}\]and that $f(n) \ll n^{3/2}$ almost surely?
-/

namespace Erdos1155

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos1155
