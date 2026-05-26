import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 671

*Reference:* https://www.erdosproblems.com/671

Given $a_{i}^n\in [-1,1]$ for all $1\leq i\leq nIs there such a sequence of $a_i^n$ such that for every continuous $f:[-1,1]\to \mathbb{R}$ there exists some $x\in [-1,1]$ where\[\limsup_{n\to \infty} \sum_{1\leq i\leq n}\lvert p_{i}^n(x)\rvert=\infty\]and yet\[\mathcal{L}^nf(x) \to f(x)?\]Is there such a sequence such that\[\limsup_{n\to \infty} \sum_{1\leq i\leq n}\lvert p_{i}^n(x)\rvert=\infty\]for every $x\in [-1,1]$ and yet for every continuous $f:[-1,1]\to \mathbb{R}$ there exists $x\in [-1,1]$ with\[\mathcal{L}^nf(x) \to f(x)?\]
-/

namespace Erdos671

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos671
