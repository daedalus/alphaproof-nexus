/-
  Population Member 01: Strategy = parity/modular obstruction for even n
  Approach: Show that if n is even then n, n+1, n+2 cannot all be powerful.
    - If n is even then 2|n, and since n is powerful, 4|n, so n ≡ 0 mod 4.
    - Then n+2 ≡ 2 mod 4, so 2|n+2 but 4∤n+2, contradicting powerfulness of n+2.
    - Thus n cannot be even. The odd case remains open.
  Rating (initial): Elo 1200
-/

import Mathlib
open Nat

namespace Erdos364

/-- A natural number n is powerful if every prime dividing n also divides it squared. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p^2 ∣ n

/-- If 2∣n and n is powerful, then 4∣n. -/
lemma two_dvd_powerful_imp_four_dvd (n : ℕ) (h : Powerful n) (h2 : 2 ∣ n) : 4 ∣ n :=
  h 2 Nat.prime_two h2

/-- No triple of consecutive powerful numbers exists when 2∣n. -/
lemma no_triple_even_n : ¬ ∃ (n : ℕ), 2 ∣ n ∧ Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) := by
  rintro ⟨n, h2n, hn, hnp1, hnp2⟩
  have h4n : 4 ∣ n := two_dvd_powerful_imp_four_dvd n hn h2n
  have : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4n
  have h_mod_np2 : (n+2) % 4 = 2 := by omega
  have h2_np2 : 2 ∣ (n+2) := by
    have : (n+2) % 2 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  have h4_np2 : 4 ∣ (n+2) := hnp2 2 Nat.prime_two h2_np2
  have : (n+2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4_np2
  omega

/-- The main conjecture: no triple of consecutive powerful numbers.
    Proven when n is even; the odd n case remains open. -/
theorem erdos_364 : ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) := by
  -- EVOLVE-BLOCK-START
  intro h
  rcases h with ⟨n, hn, hnp1, hnp2⟩
  by_cases h2n : 2 ∣ n
  · apply no_triple_even_n
    exact ⟨n, h2n, hn, hnp1, hnp2⟩
  · -- n is odd: the hard case
    -- EVOLVE-VALUE-START
    sorry
    -- EVOLVE-VALUE-END
  -- EVOLVE-BLOCK-END

end Erdos364
