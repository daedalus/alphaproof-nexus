import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 562

*Reference:* https://www.erdosproblems.com/562

Let $R_r(n)$ denote the $r$-uniform hypergraph Ramsey number: the minimal $m$ such that if we $2$-colour all edges of the complete $r$-uniform hypergraph on $m$ vertices then there must be some monochromatic copy of the complete $r$-uniform hypergraph on $n$ vertices.Prove that, for $r\geq 3$,\[\log_{r-1} R_r(n) \asymp_r n,\]where $\log_{r-1}$ denotes the $(r-1)$-fold iterated logarithm. That is, does $R_r(n)$ grow like\[2^{2^{\cdots n}}\]where the tower of exponentials has height $r-1$?
-/

namespace Erdos562

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos562
