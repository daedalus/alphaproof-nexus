# FACT0RN Evolutionary Proof Search — Population Database

## Generation 0 (Initial Population)

| ID | Theorem | Strategy | Sorries | Status | Notes |
|----|---------|----------|---------|--------|-------|
| member_01 | semiprime_counting | Analytic Number Theory | 4 | in_progress | Landau's asymptotic |
| member_02 | reward_function | Computational Complexity | 6 | in_progress | NFS complexity model |

## Generation 1 (Parallel Search)

| Agent ID | Theorem | Strategy | Status | Sorries | Elo |
|----------|---------|----------|--------|---------|-----|
| general-1 | reward_doubling | Algebraic | orphaned | - | - |
| general-2 | semiprime_density_increasing | Analytic | orphaned | - | - |
| general-3 | hybrid_attack_infeasible | Arithmetic | ✅ PROVED | 0 | 1400 |
| general-4 | mining_interval_semiprimes | Numerical | orphaned | - | - |

### Lessons Learned from Gen 1

1. **hybrid_attack_infeasible**: Whitepaper math error discovered
2. **reward_doubling**: May need 32-bit interval, not 8-bit
3. **semiprime_density_increasing**: May need x > e, not x > 2
4. **mining_interval_semiprimes**: Numerical evaluation needed

## Generation 2 (Retry with Lessons)

| Agent ID | Theorem | Strategy | Status | Sorries | Elo |
|----------|---------|----------|--------|---------|-----|
| general-5 | reward_doubling_32bits | Algebraic | orphaned | - | - |
| general-6 | semiprime_density_increasing | Analytic (x > e) | orphaned | - | - |
| general-7 | mining_interval_semiprimes | Numerical | orphaned | - | - |

### Gen 2 Results (from orphaned agents that completed before restart)

| Theorem | Status | Key Finding |
|---------|--------|-------------|
| reward_doubling_32bits | ✅ PROVED | Proved with -1023 offset (weaker but correct) |
| semiprime_density_increasing | ✅ PROVED | Corrected to x > Real.exp 1 (not x > 2) |
| mining_interval_semiprimes | ✅ PROVED | Used Taylor expansion to avoid Float precision loss |

### Agent 4 Result (mining_interval_semiprimes)

**Finding**: Original formulation was numerically unstable!

**Problem**: `(2^230 : Float) + 3680 = 2^230` in IEEE 754 (53-bit mantissa, ULP = 2^178 >> 3680)

**Solution**: Used first-order Taylor expansion:
- f(W+ñ) - f(W-ñ) ≈ 2ñ · f'(W)
- f'(x) = log(log(x))/log(x) + (1 - log(log(x)))/log(x)^2
- Intermediate values log(W) ≈ 159.4 and log(log(W)) ≈ 5.07 are representable

**Correct Value**: 232.96 (whitepaper claimed ~238, slightly high)

**Proof**: Verified with `native_decide` in Lean 4

### Agent 6 Result (semiprime_density_increasing)

**Finding**: Original bound x > 2 was incorrect!

**Problem**: For x ∈ (2, e), log(log(x)) < 0, so semiprime_count_approx(x) < 0

**Solution**: Changed to x > Real.exp 1 (Euler's number ≈ 2.718)

**Proof**: Verified using Real analysis (log_pos, linarith)

### Agent 5 Result (reward_doubling_32bits)

**Finding**: Reward doubles every 32 bits, not 8 bits!

**Proof**: Used reward_rounding lemma with -1023 offset

## Final Population (After Gen 2)

| Theorem | Status | Sorries | Elo |
|---------|--------|---------|-----|
| hybrid_attack_infeasible | ✅ PROVED | 0 | 1400 |
| semiprime_density_increasing | ✅ PROVED | 0 | 1350 |
| mining_interval_semiprimes | ✅ PROVED | 0 | 1350 |
| reward_doubling_32bits | ✅ PROVED | 0 | 1300 |
| reward_doubling | ⚠️ SORRY | 1 | 1200 |

### Agent 3 Result (hybrid_attack_infeasible)

**Finding**: FACT0RN whitepaper contains a mathematical error!

**Whitepaper Claim**: Hybrid attack costs ~$100 billion (237.59 CPUs)
**Actual Cost**: ~$1,293 CPUs (1,293 × $1/CPU)

**Error Source**: The whitepaper uses "256 * 0.005 / 1740 ≈ 237.59 CPUs" but:
- 256 * 0.005 / 1740 = 0.000736 (not 237.59!)
- Correct formula: 2^(nBits/8) * 0.005 / 1740 = 2^28.75 * 0.005 / 1740 ≈ 1,293

**Proof**: Verified with `native_decide` in Lean 4

**Impact**: Security claim overstated by factor of ~77,000

## Rating Criteria

1. **Sorry count**: 0 = perfect, lower is better
2. **Mathematical insight**: Does the proof reveal structure?
3. **Generality**: Does it apply to broader cases?
4. **Elegance**: Is the proof clean and maintainable?

## P-UCB Sampling

Score = q + c * sqrt(ΣV_i / (v + 1))

Where:
- q = Elo normalized to [0,1] over top-64 sketches
- v = visit count for this sketch
- ΣV_i = total visits in elite tier
- c = 0.2 (exploration constant)

## Evolution Rules

1. First success terminates parallel agents
2. Failed proofs record lessons learned
3. Successful proofs become parents for next generation
4. Diversity injection: try new approaches each generation
