import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 708

*Reference:* https://www.erdosproblems.com/708

Let $g(n)$ be minimal such that for any $A\subseteq [2,\infty)\cap \mathbb{N}$ with $\lvert A\rvert =n$ and any set $I$ of $\max(A)$ consecutive integers there exists some $B\subseteq I$ with $\lvert B\rvert=g(n)$ such that\[\prod_{a\in A} a \mid \prod_{b\in B}b.\]Is it true that\[g(n) \leq (2+o(1))n?\]Or perhaps even $g(n)\leq 2n$?
-/

namespace Erdos708

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos708
