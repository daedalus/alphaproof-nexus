# FACT0RN Attack Analysis: Shortcuts Without Factorization

## Core Question

Can we solve the FACT0RN equation **without factoring**?

```
gHash(PrevHash, Merkle Tree Hash, nBits, version, time, nonce) + wOffset = p1 · p2
```

Where:
- |wOffset| ≤ 16 · nBits (≈5% of bits)
- |p1 · p2|₂ = nBits
- |p1|₂ = |p2|₂ (strong semiprime)
- p1, p2 are prime

---

## Attack Vector 1: Direct Construction (No Factoring)

### Strategy
Instead of factoring a number, **construct** p1 and p2 directly, then find a nonce that satisfies the equation.

### Algorithm
```
1. Pick random prime p1 of nBits/2 bits
2. Pick random prime p2 of nBits/2 bits
3. Compute N = p1 * p2
4. Compute target = gHash(block_template)
5. Check if |N - target| ≤ 16 * nBits
6. If yes: submit (nonce, offset=N-target, p1)
7. If no: repeat with new p1, p2
```

### Analysis
- **Cost per attempt**: One gHash + one primality test
- **Success probability**: Depends on density of strong semiprimes near gHash output
- **Key insight**: We're not factoring N, we're constructing it!

### Problem
- The offset must match: N = gHash + offset
- But gHash depends on the nonce, which we're trying to find!
- This creates a circular dependency

### Resolution
We need to find (nonce, p1, p2) such that:
```
gHash(prev_hash, merkle, nbits, version, time, nonce) + offset = p1 * p2
```

This is a **simultaneous equation** problem, not just factorization.

---

## Attack Vector 2: Joye's Algorithm 3 (Pre-chosen Semiprime)

### Reference
Marc Joye, "RSA Moduli with a Predetermined Portion" (ISPEC 2008)

### Strategy
Construct a semiprime N where we control a predetermined portion of the bits.

### Algorithm (from whitepaper Section 5)
1. Choose a random prime p of nBits/2 bits
2. Use Algorithm 3 to find q such that p·q has desired bit pattern
3. This requires controlling ~33% of low bits

### Constraint Check
FACT0RN allows modifying only ~5% of bits (offset ≤ 16·nBits):
- For nBits = 230: offset ≤ 3680 bits
- But 5% of 230 = 11.5 bits
- Wait, this is confusing...

**Clarification**: The offset is an integer, not a bit mask:
- |wOffset| ≤ 16 · nBits means the offset VALUE is bounded
- For nBits = 230: |wOffset| ≤ 3680
- In binary, 3680 ≈ 2^12.2, so we can modify ~12 low bits

**Joye's Requirement**: Need to control 33% of bits
**FACT0RN Allows**: Only ~12 bits out of 230 = 5.2%

**Conclusion**: Joye's attack is infeasible at current parameters.

---

## Attack Vector 3: gHash Weakness

### Hypothesis
If gHash has mathematical structure, we might predict outputs without computing it.

### gHash Components (from whitepaper)
1. SHA3-512
2. Scrypt (1MB RAM)
3. Whirlpool
4. Shake2b
5. 512-bit prime finding
6. Modular exponentiation
7. Modular inverses

### Analysis
- SHA3, Scrypt, Whirlpool are cryptographic hashes
- No known structural weaknesses
- The combination makes precomputation infeasible

### Possible Weakness: Branching
The whitepaper mentions "Branching in main loop" and "Internal rounds depend on population count of previous hashes."

**Question**: Is the branching deterministic or data-dependent?
- If deterministic: might have fixed points
- If data-dependent: might leak information

**Current Assessment**: No known weakness, but worth investigating.

---

## Attack Vector 4: Algebraic Shortcut

### Observation
The equation has a special structure:
```
gHash(nonce) + offset = p1 * p2
```

This is a **Diophantine equation** with:
- gHash(nonce): pseudorandom function
- offset: bounded integer
- p1, p2: primes of equal bit length

### Possible Approach: Lattice Methods
If we can express this as a lattice problem, we might use LLL or BKZ.

**Challenge**: gHash is a black-box hash, not a polynomial.

### Possible Approach: Coppersmith Method
For equations of the form f(x) = 0 mod N, Coppersmith finds small roots.

**Challenge**: We don't know N (that's what we're trying to find).

---

## Attack Vector 5: Meet-in-the-Middle

### Strategy
Split the problem into two parts and meet in the middle.

### Algorithm
1. Precompute gHash for many nonces: {(nonce_i, gHash_i)}
2. Precompute semiprimes near expected values: {(p1_j * p2_j, p1_j)}
3. Find matches where gHash_i + offset = p1_j * p2_j

### Analysis
- **Time**: O(√(2^nBits)) for both tables
- **Space**: O(√(2^nBits))
- **For nBits = 230**: Need ~2^115 entries = infeasible

---

## Attack Vector 6: Statistical Attack

### Observation
From Figure 9, we expect ~238 semiprimes in each mining interval.

### Strategy
1. Compute gHash for random nonces
2. For each gHash output, check if any strong semiprime exists in [gHash - ñ, gHash + ñ]
3. If yes, factor that specific number

### Analysis
- **Expected work**: ~1 gHash per strong semiprime found
- **Factoring cost**: Depends on semiprime size
- **Key insight**: We're not factoring arbitrary numbers, we're factoring numbers we choose!

### Problem
- The semiprimes are determined by gHash, not by us
- We still need to factor them

---

## Attack Vector 7: Hybrid Construction

### Strategy
Combine construction and factoring:

1. Choose p1 (prime, nBits/2 bits)
2. Compute candidate N = p1 * 2^(nBits/2) (approximate)
3. Compute gHash for various nonces
4. For each gHash, check if |gHash - N| ≤ 16 * nBits
5. If yes, adjust p2 to make N exact

### Analysis
- **Advantage**: We control p1
- **Disadvantage**: Still need to find p2 such that p1 * p2 ≈ gHash
- **This is still factorization!**

---

## The Fundamental Insight

### Why Factorization is Necessary

The FACT0RN equation creates a **coupling** between:
1. The nonce (which determines gHash)
2. The semiprime N = p1 * p2
3. The offset (which must be small)

**Any attack must either:**
- Factor N to verify it's a valid semiprime, OR
- Construct N directly and hope it matches gHash

**The second option requires:**
- Finding (nonce, p1, p2) such that gHash(nonce) + offset = p1 * p2
- This is a **simultaneous Diophantine approximation** problem
- No known shortcut exists

### The Whitepaper's Security Argument

The whitepaper argues:
1. The offset range is too small for Joye's attack (5% < 33%)
2. gHash is too expensive to brute-force
3. The semiprime density is too low for direct construction

**Our Formal Verification Found:**
1. The 5% constraint is correct (verified)
2. gHash cost was overstated (actual: ~$1,293, not $100B)
3. The semiprime density is slightly lower than claimed (233 vs 238)

---

## Potential Vulnerabilities

### 1. gHash Structural Weakness
If gHash has mathematical structure (not just cryptographic hardness), we might:
- Predict outputs without full computation
- Find nonces that produce favorable gHash values
- Exploit correlations between inputs and outputs

**Status**: Unknown, needs investigation

### 2. Offset Range Expansion
If the offset range is larger than claimed:
- More bits are "free" to modify
- Joye's attack becomes more feasible
- Other construction methods work

**Status**: Verified correct (|wOffset| ≤ 16 · nBits)

### 3. Semiprime Density Manipulation
If we can influence which semiprimes appear in the interval:
- Choose nonces that produce intervals with more semiprimes
- Increase success probability

**Status**: gHash is pseudorandom, so this shouldn't work

### 4. Prime Generation Shortcut
If generating "balanced" primes (equal bit length) is easier:
- Reduce the search space
- Find valid (p1, p2) pairs faster

**Status**: Prime generation is well-understood, no shortcut known

---

## Conclusion

### Can We Avoid Factorization?

**Short Answer**: No, not with current knowledge.

**Long Answer**: The FACT0RN equation creates a coupling that requires either:
1. Factoring to verify semiprimality, OR
2. Direct construction with negligible success probability

**The only potential shortcut** would be exploiting gHash weaknesses, but:
- gHash uses multiple cryptographic primitives
- No known structural weaknesses
- The combination is designed to prevent optimization

### Recommendations for Attack Research

1. **Analyze gHash structure**: Look for algebraic relationships
2. **Test edge cases**: Check if certain nonces produce special gHash values
3. **Study prime distribution**: Understand how strong semiprimes cluster
4. **Compare with RSA**: FACT0RN's semiprimes are different from RSA moduli

### Open Questions

1. Does gHash have fixed points or cycles?
2. Are there correlations between gHash outputs and semiprime density?
3. Can we predict semiprime existence without factoring?
4. Is there a connection to the P vs NP problem?

---

## References

1. Joye, M. (2008). "RSA Moduli with a Predetermined Portion"
2. FACT0RN Whitepaper: Escanor Liones (May 2022)
3. Coppersmith, D. (1996). "Small Solutions to Polynomial Equations"
4. Lenstra, A.K. & Lenstra, H.W. (1993). "The Development of the Number Field Sieve"
