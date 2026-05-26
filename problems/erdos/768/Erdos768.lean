import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 768

*Reference:* https://www.erdosproblems.com/768

Let $A\subset\mathbb{N}$ be the set of $n$ such that for every prime $p\mid n$ there exists some $d\mid n$ with $d>1$ such that $d\equiv 1\pmod{p}$. Is it true that there exists some constant $c>0$ such that for all large $N$\[\frac{\lvert A\cap [1,N]\rvert}{N}=\exp(-(c+o(1))\sqrt{\log N}\log\log N).\]
-/

namespace Erdos768

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos768
