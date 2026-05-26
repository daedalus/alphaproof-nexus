import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 917

*Reference:* https://www.erdosproblems.com/917

Let $k\geq 4$ and $f_k(n)$ be the largest number of edges in a graph on $n$ vertices which has chromatic number $k$ and is critical (i.e. deleting any edge reduces the chromatic number).Is it true that\[f_k(n) \gg_k n^2?\]Is it true that\[f_6(n)\sim n^2/4?\]More generally, is it true that, for $k\geq 6$,\[f_k(n) \sim \frac{1}{2}\left(1-\frac{1}{\lfloor k/3\rfloor}\right)n^2?\]
-/

namespace Erdos917

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos917
