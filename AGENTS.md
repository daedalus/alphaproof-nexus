# AlphaProof Nexus — AGENTS.md

Open conjecture: **Does every congruence-avoiding set have a logarithmic density?**
(Erdos Problem #25, [erdosproblems.com/25](https://www.erdosproblems.com/25))

This repo applies AlphaProof Nexus (arXiv:2605.22763) evolutionary proof search in Lean 4.
Evolve a population of proof attempts; rate by "sorry" count and mathematical insight.

## Quick start

```bash
lean Erdos25-evolve/Erdos25.lean                    # Problem statement + stubs
lean Erdos25-evolve/population/member_04_gen1_head_truncation.lean  # Champion
```

Requires Lean 4.29.1, `lean` on `PATH`.

## File structure

```
Erdos25.lean                              — Top-level problem (external FormalConjectures dep)
Erdos25-evolve/
  Erdos25.lean                            — Self-contained problem + HasLogDensity definition
  population/                             — Generations of proof attempts
    member_{NN}_{description}.lean        — Population member naming
    member_{NN}_gen{G}_{description}.lean — Later-gen member naming
ErdosLib/                                 — Reusable library (namespaced under ErdosLib)
  Density.lean                            — HasDensity, HasLogDensity, upper/lower variants
  Problem.lean                            — Answer type, research_open attribute
  Periodic.lean, Truncation.lean, Summability.lean
```

## Population member conventions

Every population file begins with a header doc-comment:

```lean
/-
  Population Member NN: Strategy = ...
  Approach: ...
  Rating (initial): Elo 1200
-/
```

Each file is self-contained (imports `Mathlib`), defines its own `HasLogDensity`, `A`, etc.
EVOLVE-BLOCK-START / EVOLVE-BLOCK-END comments mark editable regions.

## How to add a new population member

1. Pick a description and next number (scan `population/` for the highest `NN`).
2. Create `Erdos25-evolve/population/member_{NN}_gen{G}_{description}.lean`.
3. Copy the header block from an existing member; update Strategy, Approach, Rating.
4. Import `Mathlib`, open `Filter` `Finset` `Real` `Set` `Topology`.
5. Define `HasLogDensity`, `A`, `UniversalStatement` (match existing signature).
6. Mark editable sections with `-- EVOLVE-BLOCK-START` / `-- EVOLVE-BLOCK-END`.
7. Decorate the main theorem with `@[research_open]`.
8. Compile with `lean` before considering it done.

## How to use ErdosLib

Reusable lemmas live in `ErdosLib/` under `namespace ErdosLib`:
- `HasLogDensity`, `HasDensity`, `upperDensity`, `lowerDensity`
- `hasDensity_iff`, `hasLogDensity_iff`, `nat_density_imp_log_density`
- `A_from_seqs` set builder, `EventuallyPeriodic`, `A_head` truncation, `TailSumZero`

Import via `import ErdosLib` (not `import Mathlib` alone) when using library definitions.
This isn't required — population members are self-contained and typically ignore ErdosLib.

## Rules

❌ Don't write `HasLogDensity` / `A` / `UniversalStatement` with different signatures.
✅ Keep signatures identical to `Erdos25-evolve/Erdos25.lean` for cross-comparison.

❌ Don't remove EVOLVE-BLOCK markers — they delimit the agent-editable region.
✅ Put all new lemmas and proof attempts inside `-- EVOLVE-BLOCK-START/END`.

❌ Don't add external dependencies or `lakefile.lean`.
✅ Keep each file compilable via `lean <filename>` with only `import Mathlib`.

❌ Don't change the `Answer` type or `research_open` attribute convention.
✅ Use `Answer.known true` / `Answer.known false` / `answer(sorry)`.

## Current champion

`member_04_gen1_head_truncation.lean` — Head-truncation approach, 10 `sorry`s.
The key open condition: **tail sum Σ_{i>k} 1/n_i → 0 as k → ∞** determines the answer.
