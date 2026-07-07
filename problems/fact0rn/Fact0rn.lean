import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-
  FACT0RN Blockchain -- Mathematical Formalization
  Based on: "FACT0RN: Integer Factorization as Proof of Work" (Escanor Liones, May 2022)

  This file formalizes the core mathematical claims from the FACT0RN whitepaper
  that could be verified or disproven using formal theorem proving.
-/

namespace Fact0rn

def reward_function (p1_bits : Nat) : Nat :=
  let base := 11178600 * 2^((p1_bits + (p1_bits % 2)) / 32)
  (base / 1024) * 1024 + 1023

-- EVOLVE-BLOCK-START

/-- Reward doubles every 64 additional bits in factor size.

    When p1_bits increases by 64, the exponent e = (p1_bits + p1_bits%2) / 32
    increases by exactly 2 (since 64 is even and 64/32=2), so the base
    11178600 * 2^e quadruples (×4). The floor rounding loses at most 1023,
    and the ×4 amplification overwhelms this error. -/
theorem reward_doubling :
    ∀ (p1_bits : Nat),
      reward_function (p1_bits + 64) ≥ 2 * reward_function p1_bits := by
  intro p1_bits
  unfold reward_function
  set e := (p1_bits + p1_bits % 2) / 32
  have h_exp : (p1_bits + 64 + (p1_bits + 64) % 2) / 32 = e + 2 := by
    subst e; omega
  -- Convert (n/1024)*1024 to n - n%1024 so omega can reason about division
  have h_id : ∀ n : Nat, (n / 1024) * 1024 = n - n % 1024 := by intro; omega
  simp only [h_exp, Nat.pow_add, show (2:Nat) ^ 2 = 4 from by norm_num, Nat.mul_comm, h_id]
  omega

/-- 32-bit bound: reward(p+32) ≥ 2·reward(p) − 1023.

    The reward base doubles when p1_bits increases by 32 (exponent increases by 1),
    but the ⌊·⌋₁₀₂₄ rounding introduces at most a 1023 deficit. -/
theorem reward_doubling_32bits :
    ∀ (p1_bits : Nat),
      reward_function (p1_bits + 32) ≥ 2 * reward_function p1_bits - 1023 := by
  intro p1_bits
  unfold reward_function
  set e := (p1_bits + p1_bits % 2) / 32
  have h_exp : (p1_bits + 32 + (p1_bits + 32) % 2) / 32 = e + 1 := by
    subst e; omega
  have h_id : ∀ n : Nat, (n / 1024) * 1024 = n - n % 1024 := by intro; omega
  simp only [h_exp, Nat.pow_succ, h_id]
  omega

-- EVOLVE-BLOCK-END

theorem fact0rn_soundness : True := trivial

end Fact0rn
