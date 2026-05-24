# AlphaProof Nexus — Erdős Problem #25

**Does every congruence-avoiding set have a logarithmic density?**
[erdosproblems.com/25](https://www.erdosproblems.com/25) — Open, $0 prize.

This repo applies the [AlphaProof Nexus](https://arxiv.org/abs/2605.22763) evolutionary
methodology to decompose and attack the problem in Lean 4.

## Population (3 generations, 10 members)

| Gen | Members | Contribution |
|-----|---------|--------------|
| 0 | 5 | Baseline strategies: DE case, Cauchy criterion, counterexample sketch, head-truncation (2 variants), summability |
| 1 | 2 | **Head-truncation** (keep first k moduli) identified as the correct decomposition; tail-truncation was wrong |
| 2 | 2 | Hybrid: head-truncation + measure-theoretic bounds |
| 3 | 1 | Counterexample exploration via Σ 1/n_i divergence |

## Key Finding

The problem reduces to a single open condition: $\sum_{i > k} 1/n_i \to 0$ as $k \to \infty$.
Head-truncation shows density exists whenever this tail sum converges.
The gap is whether a subtler proof handles the divergent case (answer = True)
or a counterexample with slow-growing $n_i$ exists (answer = False).

## Compile

```bash
lean Erdos25.lean                     # Top-level statement + stubs
lean Erdos25-evolve/Erdos25.lean      # Self-contained version
lean population/member_04_gen1_head_truncation.lean  # Champion (10 sorries)
```

Requires Lean 4.29.1, `lean` on `PATH`.

## Structure

```
Erdos25.lean                                          — Problem statement, DE lemma, counterexample
Erdos25-evolve/
  Erdos25.lean                                        — Self-contained problem + HasLogDensity
  population/
    member_04_gen1_head_truncation.lean               — 🏆 Champion
    member_01_DE_base.lean ... member_09_gen3_counterexample.lean  — Other members
```

## Status

All members compile. Champion has 10 `sorry`s: 3 standard (epsilon-delta), 6 structural,
1 **mathematically open** (tail sum convergence).
