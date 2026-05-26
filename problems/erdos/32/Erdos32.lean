import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 32

*Reference:* https://www.erdosproblems.com/32

Is there a set $A\subset\mathbb{N}$ such that\[\lvert A\cap\{1,\ldots,N\}\rvert = o((\log N)^2)\]and such that every large integer can be written as $p+a$ for some prime $p$ and $a\in A$? Can the bound $O(\log N)$ be achieved? Must such an $A$ satisfy\[\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{\log N}> 1?\]
-/

namespace Erdos32

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos32
