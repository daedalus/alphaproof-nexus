import Mathlib

open Set Finset
open scoped BigOperators

/-!
# Erdős Problem 180

*Reference:* https://www.erdosproblems.com/180

If $\mathcal{F}$ is a finite set of finite graphs then $\mathrm{ex}(n;\mathcal{F})$ is the maximum number of edges a graph on $n$ vertices can have without containing any subgraphs from $\mathcal{F}$. Note that it is trivial that $\mathrm{ex}(n;\mathcal{F})\leq \mathrm{ex}(n;G)$ for every $G\in\mathcal{F}$. Is it true that, for every $\mathcal{F}$, there exists $G\in\mathcal{F}$ such that\[\mathrm{ex}(n;G)\ll_{\mathcal{F}}\mathrm{ex}(n;\mathcal{F})?\]
-/

namespace Erdos180

-- EVOLVE-BLOCK-START
-- EVOLVE-BLOCK-END

end Erdos180
