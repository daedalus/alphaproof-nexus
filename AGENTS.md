# AlphaProof Nexus — AGENTS.md

Repository of Lean 4 formalizations for open Erdős problems, evolved via
AlphaProof Nexus (arXiv:2605.22763) evolutionary proof search.

Each problem lives in its own directory with a population of proof attempts
rated by "sorry" count and mathematical insight.

## Quick start

```bash
# Erdos #25 — congruence-avoiding sets
lean Erdos25-evolve/Erdos25.lean
lean Erdos25-evolve/population/member_04_gen1_head_truncation.lean

# Erdos #634 — triangle tilings
lean Erdos634/Erdos634.lean
lean Erdos634/population/member_07_gen7_geometric_obstruction.lean

# Erdos #1 — sum-distinct sets
lean Erdos1/Erdos1.lean
lean Erdos1/population/member_05_champion.lean
```

Requires Lean 4.29.1, `lean` on `PATH`.

## File structure

```
Erdos1/                                   — Problem directory for Erdős #1
  Erdos1.lean                             — Problem statement + @[research_open] stub
  population/member_{NN}_{desc}.lean      — Proof attempts
Erdos25-evolve/                           — Problem directory for Erdős #25
  Erdos25.lean                            — Self-contained problem + HasLogDensity
  population/member_{NN}_{desc}.lean      — Proof attempts (may have gen{G} tags)
ErdosLib/                                 — Shared library (namespace ErdosLib)
  proven/                                 — Fully proven lemmas (0 sorries)
    Problem.lean, SumDistinct.lean
  unproven/                               — Lemmas with open sorries
    Density.lean, Periodic.lean, Truncation.lean, Summability.lean
Erdos25.lean                              — Top-level Erdos #25 (external FormalConjectures dep)
```

Each new problem gets its own `Erdos{N}/` directory with the same structure.

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

1. Create `Erdos{N}/Erdos{N}.lean` with the problem statement.
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
| #1 — sum-distinct sets | `Erdos1/` | 5 | 1 | `member_05_champion.lean` | Proof complete (0 sorries) |
| #25 — congruence-avoiding sets | `Erdos25-evolve/` | 12 | 5 | `member_04_gen1_head_truncation.lean` | 10 sorries (1 mathematically open) |
| #634 — triangle tilings | `Erdos634/` | 7 | 7 | `member_07_gen7_geometric_obstruction.lean` | 0 errors, 3 sorries (member_07 exposes formalization gap: `tilable_all_pos` contradicts `not_tilable_7` under weak TriangleTilable; geometric obstruction lemmas restated under GeometricTriangleTilable) |
