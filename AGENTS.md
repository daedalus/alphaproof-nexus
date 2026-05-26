# AlphaProof Nexus — AGENTS.md

Repository of Lean 4 formalizations for open Erdős problems, evolved via
AlphaProof Nexus (arXiv:2605.22763) evolutionary proof search.

Each problem lives under `problems/N/` with a population of proof attempts
rated by "sorry" count and mathematical insight.

## Quick start

```bash
# Erdos #25 — congruence-avoiding sets
lean problems/25/Erdos25.lean
lean problems/25/population/member_04_gen1_head_truncation.lean

# Erdos #634 — triangle tilings
lean problems/634/Erdos634.lean
lean problems/634/population/member_07_gen7_geometric_obstruction.lean

# Erdos #1 — sum-distinct sets
lean problems/1/Erdos1.lean
lean problems/1/population/member_05_champion.lean
```

Requires Lean 4.29.1, `lean` on `PATH`.

## File structure

```
problems/                                   — All problem directories
  1/                                        — Erdős #1
    Erdos1.lean                             — Problem statement + @[research_open] stub
    population/member_{NN}_{desc}.lean      — Proof attempts
  25/                                       — Erdős #25
    Erdos25.lean                            — Self-contained problem + HasLogDensity
    Erdos25_formal_conjectures.lean         — Variant with FormalConjectures dep
    population/member_{NN}_{desc}.lean      — Proof attempts (may have gen{G} tags)
  364/                                      — Erdős #364
    Erdos364.lean
    population/
  634/                                      — Erdős #634
    Erdos634.lean
    population/
  ...                                       — Empty dirs for other open problems
ErdosLib/                                   — Shared library (namespace ErdosLib)
  proven/                                   — Fully proven lemmas (0 sorries)
    Problem.lean, SumDistinct.lean
  unproven/                                 — Lemmas with open sorries
    Density.lean, Periodic.lean, Truncation.lean, Summability.lean
scripts/                                    — Utility scripts
```

Each new problem gets its own `problems/N/` directory with the same structure.

## Problem conventions

Every problem has:
- A namespace matching the problem (e.g. `Erdos1`, `Erdos25`)
- A `@[research_open]` theorem (the main conjecture)
- `-- EVOLVE-BLOCK-START` / `-- EVOLVE-BLOCK-END` markers around editable regions
- `answer(sorry)` or direct `sorry` for the open part

Every population member has a header doc-comment:

```lean
/-
  Population Member NN: Strategy = ...
  Approach: ...
  Rating (initial): Elo 1200
-/
```

Files are self-contained (import `Mathlib` only, no external deps).

## How to add a new problem

1. Create `problems/N/Erdos{N}.lean` with the problem statement.
2. Define namespace, types, the main `@[research_open]` theorem, and EVOLVE-BLOCK markers.
3. Add a `population/` subdirectory.
4. Add an entry to `ErdosLib/Problem.lean` if reusable types apply.

## How to add a new population member

1. Scan the problem's `population/` for the highest `NN`.
2. Create `member_{NN}_gen{G}_{description}.lean`.
3. Copy the header block from an existing member; update Strategy, Approach, Rating.
4. Import `Mathlib`, define relevant types (match problem signature).
5. Mark editable sections with `-- EVOLVE-BLOCK-START` / `-- EVOLVE-BLOCK-END`.
6. Decorate the main theorem with `@[research_open]`.
7. Compile with `lean` before considering it done.

## How to use ErdosLib

Reusable lemmas live in `ErdosLib/` under `namespace ErdosLib`:
- `HasLogDensity`, `HasDensity`, `upperDensity`, `lowerDensity`, `HasLogDensity`
- `Answer` (`unknown` / `true` / `false`), `A_from_seqs`, `UniversalStatement`
- `EventuallyPeriodic`, `A_head`, `TailSumZero`
- `IsSumDistinctSet`, `subset_sums`, `trivial_bound`, `powers_of_two_set` (from `SumDistinct.lean`)
- `active_constraints_finite`, `f`, `f_nonneg`, `f_le_one`, `mem_A_iff_f_zero` (from `Problem.lean`)
- `finite_has_density_zero`, `S`, `S_equiv`, `log_one_add_x_ge_x_div_one_add_x` (from `Density.lean`)

Import via `import ErdosLib` (e.g., in `ErdosLib/` submodules or cross-problem files).
Submodule imports use the full path: `import ErdosLib.unproven.Density`, `import ErdosLib.proven.Problem`.
Population members are self-contained and typically ignore ErdosLib.

## Rules

❌ Don't write signatures that diverge from the problem's own `Erdos{N}.lean`.
✅ Keep statements consistent for cross-comparison across members.

❌ Don't remove EVOLVE-BLOCK markers — they delimit the editable region.
✅ Put all new lemmas and proof attempts inside `-- EVOLVE-BLOCK-START/END`.

❌ Don't add external dependencies or `lakefile.lean`.
✅ Keep each file compilable via `lean <filename>` with only `import Mathlib`.

❌ Don't invent a new `Answer` type per problem.
✅ Use `Answer.true` / `Answer.false` / `answer(sorry)` from `ErdosLib` if applicable,
   or the problem's own inductive if self-contained.

## Current problems

| Problem | Dir | Members | Gens | Champion | Status |
|---------|-----|---------|------|----------|--------|
| #1 — sum-distinct sets | `problems/1/` | 5 | 1 | `member_05_champion.lean` | 0 errors, 7 sorries across files |
| #25 — congruence-avoiding sets | `problems/25/` | 12 | 5 | `member_04_gen1_head_truncation.lean` | 10 sorries (1 mathematically open) |
| #364 — consecutive powerful numbers | `problems/364/` | 3 | 3 | `member_03_gen3_modular_framework.lean` | 0 errors, 1 sorry (even n closed; odd n: 9 admissible CRT classes mod 900, all non‑empty) |
| #634 — triangle tilings | `problems/634/` | 9 | 9 | `member_09_gen9_n_two_bisection.lean` | 0 errors, 3 sorries (member_09 adds n=2 bisection + Congruent 6-permutation; 3 obstruction sorries remain under `GeometricTriangleTilable`) |
