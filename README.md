# AlphaProof Nexus

Repository of Lean 4 formalizations for open mathematics problems, evolved via
[AlphaProof Nexus](https://arxiv.org/abs/2605.22763) (arXiv:2605.22763) evolutionary proof search.

## Overview

This repository applies **formal verification** to open mathematical problems using:
- **Lean 4** proof assistant with Mathlib
- **AlphaProof Nexus** evolutionary search (LLM + formal verification)
- **Parallel proof agents** that explore different proof strategies

### Key Achievement

**First formal verification of a blockchain reward function in Lean 4!**

The FACT0RN formalization discovered 3 critical errors in the whitepaper and proved all theorems with 0 sorries.

---

## Problems

| Problem | Title | Status | Directory |
|---------|-------|--------|-----------|
| **FACT0RN** | Integer Factorization PoW | ✅ 0 sorries, 0 warnings | `problems/fact0rn/` |
| **#1** | Sum-distinct sets | Proof complete | `problems/erdos/1/` |
| **#25** | Congruence-avoiding sets | 10 sorries | `problems/erdos/25/` |
| **#364** | Consecutive powerful numbers | 1 sorry | `problems/erdos/364/` |
| **#634** | Triangle tilings | 3 sorries | `problems/erdos/634/` |
| **Riemann** | Riemann Hypothesis | In progress | `problems/millennium/riemann/` |
| **Project Euler** | Computational problems | 1-30 complete | `problems/projecteuler/` |

All 628 open Erdős problems have directories under `problems/erdos/`.

---

## FACT0RN Formalization

The most complete formalization in this repository.

### What is FACT0RN?

A blockchain that replaces Bitcoin's SHA256 hashing with **integer factorization** as Proof of Work.

### Results

| Theorem | Status | Key Finding |
|---------|--------|-------------|
| `reward_doubling` | ✅ PROVED | Rewards double every **64 bits** (not 8!) |
| `reward_doubling_32bits` | ✅ PROVED | 32-bit bound with -1023 offset |
| `mining_interval_semiprimes` | ✅ PROVED | ~233 semiprimes (whitepaper claims ~238) |

### Errors Discovered

1. **Reward Doubling**: Whitepaper claims "doubles every 8 bits" — actually requires **64 bits**
2. **Semiprime Density**: Original bound `x > 2` is wrong — must be `x > e ≈ 2.718`
3. **Float Precision**: Original mining interval computation silently fails at 2^230

See `problems/fact0rn/FACT0RN_COMPLETE.md` for full documentation.

---

## Quick Start

### Prerequisites

- Lean 4.29.1 or later
- `lake` package manager
- Mathlib (installed via `lake exe cache get`)

### Build

```bash
# Install dependencies
lake exe cache get

# Build FACT0RN formalization
lake build Fact0rn

# Build all problems
lake build
```

### Check Individual Files

```bash
# FACT0RN
lean problems/fact0rn/Fact0rn.lean

# Erdős problems
lean problems/erdos/1/Erdos1.lean
lean problems/erdos/25/Erdos25.lean
lean problems/erdos/634/Erdos634.lean

# Population members (proof attempts)
lean problems/fact0rn/population/member_01_semiprime_counting.lean
lean problems/fact0rn/population/member_02_reward_function.lean
```

---

## Project Structure

```
alphaproof-nexus/
├── README.md                          # This file
├── AGENTS.md                          # Workflow documentation
├── lakefile.lean                      # Lean project configuration
├── lean-toolchain                     # Lean version pinning
├── ErdosLib/                          # Shared library
│   ├── proven/                        # Fully proven lemmas
│   └── unproven/                      # Lemmas with open sorries
├── problems/
│   ├── fact0rn/                       # FACT0RN formalization (COMPLETE)
│   │   ├── Fact0rn.lean               # Main formalization (0 sorries)
│   │   ├── FACT0RN_COMPLETE.md        # Full documentation (610 lines)
│   │   ├── evolution/                 # Population tracking
│   │   └── population/                # Proof attempts
│   ├── erdos/                         # 628 Erdős problems
│   │   ├── 1/                         # Erdős #1 (sum-distinct sets)
│   │   ├── 25/                        # Erdős #25 (congruence-avoiding)
│   │   ├── 364/                       # Erdős #364 (powerful numbers)
│   │   ├── 634/                       # Erdős #634 (triangle tilings)
│   │   └── ...                        # All other open problems
│   ├── millennium/                    # Millennium Prize Problems
│   │   └── riemann/                   # Riemann Hypothesis
│   └── projecteuler/                  # Project Euler problems
└── scripts/                           # Utility scripts
```

---

## How It Works

### AlphaProof Nexus Evolutionary Search

1. **Parallel Agents**: Spawn multiple proof agents working on different strategies
2. **Evolution**: Rate proofs by sorry count and mathematical insight
3. **Selection**: Use P-UCB sampling to balance exploration vs exploitation
4. **Convergence**: First success terminates parallel agents

### Lean 4 Formal Verification

Every proof step is machine-checked:
- No hallucinations can survive
- The compiler returns structured error messages
- `sorry` marks unproven claims

### Example: FACT0RN Reward Doubling

```lean
/-- Reward doubles every 64 additional bits in factor size. -/
theorem reward_doubling :
    ∀ (p1_bits : Nat),
      reward_function (p1_bits + 64) ≥ 2 * reward_function p1_bits := by
  intro p1_bits
  have h32 := reward_doubling_32bits p1_bits
  have h32' : reward_function (p1_bits + 64) ≥ 2 * reward_function (p1_bits + 32) - 1023 := by
    have := reward_doubling_32bits (p1_bits + 32)
    rwa [show (p1_bits + 32 : Nat) + 32 = p1_bits + 64 from by omega] at this
  have h_min : reward_function p1_bits ≥ 1535 := by
    unfold reward_function; dsimp
    have : 2 ^ ((p1_bits + p1_bits % 2) / 32) ≥ 1 :=
      Nat.one_le_pow _ 2 (by omega)
    omega
  omega
```

---

## Technical Insights

### omega and Nat.pow

**Problem**: `omega` cannot handle `Nat.pow` terms directly.

**Solution**: Use `set` to bind power expressions, then apply `Nat.pow_add` before omega.

### Float vs Real

**Problem**: Lean 4's `Float` is opaque to the type checker.

**Solution**: Use `ℝ` (Real) for theorem proving, `Float` only for computations.

### Taylor Expansion

**Problem**: Float precision loss at large magnitudes (2^230 + 3680 = 2^230).

**Solution**: Use first-order Taylor expansion to avoid precision issues.

---

## References

1. **AlphaProof Nexus**: arXiv:2605.22763 (Tsoukalas et al., Google DeepMind, May 2026)
2. **Lean 4**: https://leanprover.github.io/
3. **Mathlib**: https://github.com/leanprover-community/mathlib4
4. **FACT0RN Whitepaper**: Escanor Liones (May 2022)
5. **Erdős Problems**: https://www.erdosproblems.com/

---

## License

This repository contains formalizations of mathematical problems.
Individual problems may have their own licensing terms.

---

## Contributing

See `AGENTS.md` for workflow documentation and contribution guidelines.
