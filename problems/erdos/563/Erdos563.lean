import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 563

*Reference:* https://www.erdosproblems.com/563

Let $F(n,\alpha)$ denote the smallest $m$ such that there exists a $2$-colouring of the edges of $K_n$ so that every $X\subseteq [n]$ with $\lvert X\rvert\geq m$ contains more than $\alpha \binom{\lvert X\rvert}{2}$ many edges of each colour. Prove that, for every $0\leq \alpha< 1/2$,\[F(n,\alpha)\sim c_\alpha\log n\]for some constant $c_\alpha$ depending only on $\alpha$.
-/

namespace Erdos563

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos563
