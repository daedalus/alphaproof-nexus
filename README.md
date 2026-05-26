# AlphaProof Nexus

Repository of Lean 4 formalizations for open Erdős problems, evolved via
AlphaProof Nexus (arXiv:2605.22763) evolutionary proof search.

## Problems

| # | Title | Status | Dir |
|---|-------|--------|-----|
| 1 | Sum-distinct sets | Proof complete (0 sorries) | `problems/1/` |
| 25 | Congruence-avoiding sets | 10 sorries (1 open) | `problems/25/` |
| 364 | Consecutive powerful numbers | 0 errors, 1 sorry | `problems/364/` |
| 634 | Triangle tilings | 0 errors, 3 sorries | `problems/634/` |

All 628 open Erdős problems have directories under `problems/N/`.

## Quick start

```bash
lean problems/25/Erdos25.lean
lean problems/25/population/member_04_gen1_head_truncation.lean
lean problems/634/population/member_07_gen7_geometric_obstruction.lean
lean problems/1/Erdos1.lean
lean problems/1/population/member_05_champion.lean
```

Requires Lean 4.29.1, `lean` on `PATH`.

See `AGENTS.md` for full workflow documentation.
