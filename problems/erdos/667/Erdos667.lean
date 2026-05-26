import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 667

*Reference:* https://www.erdosproblems.com/667

Let $p,q\geq 1$ be fixed integers. We define $H(n)=H(N;p,q)$ to be the largest $m$ such that any graph on $n$ vertices where every set of $p$ vertices spans at least $q$ edges must contain a complete graph on $m$ vertices.Is\[c(p,q)=\liminf \frac{\log H(n)}{\log n}\]a strictly increasing function of $q$ for $1\leq q\leq \binom{p-1}{2}+1$?
-/

namespace Erdos667

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos667
