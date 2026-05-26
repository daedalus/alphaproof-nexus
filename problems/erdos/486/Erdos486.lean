import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 486

*Reference:* https://www.erdosproblems.com/486

Let $A\subseteq \mathbb{N}$, and for each $n\in A$ choose some $X_n\subseteq \mathbb{Z}/n\mathbb{Z}$. Let\[B = \{ m\in \mathbb{N} : m\not\in X_n\pmod{n}\textrm{ for all }n\in A\textrm{ with }m>n\}.\]Must $B$ have a logarithmic density, i.e. is it true that\[\lim_{x\to \infty} \frac{1}{\log x}\sum_{\substack{m\in B\\ m<x}}\frac{1}{m}\]exists?
-/

namespace Erdos486

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos486
