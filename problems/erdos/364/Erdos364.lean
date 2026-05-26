import Mathlib
open Nat

/-!
# Erdős Problem 364: Consecutive Powerful Numbers

**Reference:** [erdosproblems.com/364](https://www.erdosproblems.com/364)

A positive integer $n$ is *powerful* if for every prime $p \mid n$ we have $p^2 \mid n$.

**Open question:** Are there any triples of consecutive positive integers all of which
are powerful? That is, does there exist $n$ such that $n$, $n+1$, $n+2$ are all powerful?

Erdős conjectured the answer is **no**. The weak variant (no quadruple) is trivial by
mod 4 parity: one of four consecutive numbers is ≡ 2 mod 4, which cannot be powerful.

Tags: number theory, powerful.
-/

namespace Erdos364

/-- A natural number n is powerful if every prime dividing n also divides it squared. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p^2 ∣ n

/-- No quadruple of consecutive powerful numbers exists (trivial: one is ≡ 2 mod 4). -/
lemma no_powerful_quadruple : ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) ∧ Powerful (n+3) := by
  rintro ⟨n, hn, hnp1, hnp2, hnp3⟩
  have h2mod4 : n % 4 = 2 ∨ (n+1) % 4 = 2 ∨ (n+2) % 4 = 2 ∨ (n+3) % 4 = 2 := by omega
  rcases h2mod4 with (h|h|h|h)
  · have h2 : 2 ∣ n := by
      have : n % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h4 : 4 ∣ n := hn 2 Nat.prime_two h2
    have : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    omega
  · have h2 : 2 ∣ (n+1) := by
      have : (n+1) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h4 : 4 ∣ (n+1) := hnp1 2 Nat.prime_two h2
    have : (n+1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    omega
  · have h2 : 2 ∣ (n+2) := by
      have : (n+2) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h4 : 4 ∣ (n+2) := hnp2 2 Nat.prime_two h2
    have : (n+2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    omega
  · have h2 : 2 ∣ (n+3) := by
      have : (n+3) % 2 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero this
    have h4 : 4 ∣ (n+3) := hnp3 2 Nat.prime_two h2
    have : (n+3) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
    omega

/-- The main conjecture: there is no triple of consecutive powerful numbers.
    Tagged `research_open` (open Erdős problem #364). -/
theorem erdos_364 : ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) := by
  -- EVOLVE-BLOCK-START
  sorry
  -- EVOLVE-BLOCK-END

end Erdos364
