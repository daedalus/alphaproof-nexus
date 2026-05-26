import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 420

*Reference:* https://www.erdosproblems.com/420

If $\tau(n)$ counts the number of divisors of $n$ then let\[F(f,n)=\frac{\tau((n+\lfloor f(n)\rfloor)!)}{\tau(n!)}.\]Is it true that\[\lim_{n\to \infty}F((\log n)^C,n)=\infty\]for large $C$? Is it true that $F(\log n,n)$ is everywhere dense in $(1,\infty)$? More generally, if $f(n)\leq \log n$ is a monotonic function such that $f(n)\to \infty$ as $n\to \infty$, then is $F(f,n)$ everywhere dense?
-/

namespace Erdos420

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos420
