import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 489

*Reference:* https://www.erdosproblems.com/489

Let $A\subseteq \mathbb{N}$ be a set such that $\lvert A\cap [1,x]\rvert=o(x^{1/2})$. Let\[B=\{ n\geq 1 : a\nmid n\textrm{ for all }a\in A\}.\]If $B=\{b_1<b_2<\cdots\}$ then is it true that\[\lim \frac{1}{x}\sum_{b_i<x}(b_{i+1}-b_i)^2\]exists (and is finite)?
-/

namespace Erdos489

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos489
