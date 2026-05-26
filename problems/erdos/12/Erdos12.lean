import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 12

*Reference:* https://www.erdosproblems.com/12

Let $A$ be an infinite set such that there are no distinct $a,b,c\in A$ such that $a\mid (b+c)$ and $b,c>a$. Is there such an $A$ with\[\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N^{1/2}}>0?\]Does there exist some absolute constant $c>0$ such that there are always infinitely many $N$ with\[\lvert A\cap\{1,\ldots,N\}\rvert<N^{1-c}?\]Is it true that\[\sum_{n\in A}\frac{1}{n}<\infty?\]
-/

namespace Erdos12

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos12
