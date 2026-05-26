import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 1131

*Reference:* https://www.erdosproblems.com/1131

For $x_1,\ldots,x_n\in [-1,1]$ let\[l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},\]which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$.What is the minimal value of\[I(x_1,\ldots,x_n)=\int_{-1}^1 \sum_k \lvert l_k(x)\rvert^2\mathrm{d}x?\]In particular, is it true that\[\min I =2-(1+o(1))\frac{1}{n}?\]
-/

namespace Erdos1131

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos1131
