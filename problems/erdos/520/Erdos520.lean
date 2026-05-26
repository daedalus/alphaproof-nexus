import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 520

*Reference:* https://www.erdosproblems.com/520

Let $f$ be a Rademacher multiplicative function: a random $\{-1,0,1\}$-valued multiplicative function, where for each prime $p$ we independently choose $f(p)\in \{-1,1\}$ uniformly at random, and for square-free integers $n$ we extend $f(p_1\cdots p_r)=f(p_1)\cdots f(p_r)$ (and $f(n)=0$ if $n$ is not squarefree). Does there exist some constant $c>0$ such that, almost surely,\[\limsup_{N\to \infty}\frac{\sum_{m\leq N}f(m)}{\sqrt{N\log\log N}}=c?\]
-/

namespace Erdos520

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos520
