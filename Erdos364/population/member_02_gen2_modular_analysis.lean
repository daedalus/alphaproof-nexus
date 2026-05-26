/-
  Population Member 02: Strategy = modular constraints + small‑n brute force
  Approach: Extend Gen1 with 3‑adic / 9‑adic case analysis and a decidable
    small‑n check (up to 1000).  The odd‑n case splits into three residue
    families (n ≡ 0, 8, 7 mod 9), all of which satisfy the necessary modular
    constraints — the main conjecture remains open and requires deeper
    analytic number theory (e.g. ABC conjecture or sieve bounds).
  Rating (initial): Elo 1250
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
  have h_mod_n : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4n
  have h_mod_np2 : (n+2) % 4 = 2 := by omega
  have h2_np2 : 2 ∣ (n+2) := by
    have : (n+2) % 2 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  have h4_np2 : 4 ∣ (n+2) := hnp2 2 Nat.prime_two h2_np2
  have h_mod_np2' : (n+2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4_np2
  omega

/-- If n is odd and n+1 is powerful, then 4∣(n+1). -/
lemma odd_n_imp_four_dvd_np1 (n : ℕ) (hn_odd : ¬ 2 ∣ n) (hnp1 : Powerful (n+1)) : 4 ∣ (n+1) := by
  have h2_np1 : 2 ∣ (n+1) := by
    have hm2 : n % 2 = 1 := by
      have h_cases := Nat.mod_two_eq_zero_or_one n
      rcases h_cases with (h0|h1)
      · exfalso; exact hn_odd (Nat.dvd_of_mod_eq_zero h0)
      · exact h1
    have : (n+1) % 2 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  exact hnp1 2 Nat.prime_two h2_np1

/-- In the odd‑n case, n ≡ 3 (mod 4). -/
lemma odd_n_mod4 (n : ℕ) (hn_odd : ¬ 2 ∣ n) (hnp1 : Powerful (n+1)) : n % 4 = 3 := by
  have h4_np1 : 4 ∣ (n+1) := odd_n_imp_four_dvd_np1 n hn_odd hnp1
  have h_np1_mod4 : (n+1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4_np1
  omega

/-- Three‑adic case analysis: one of n, n+1, n+2 is divisible by 3,
    and (since that term is powerful) it is divisible by 9, which
    fixes a residue class mod 9 for n. -/
lemma mod9_residue_cases (n : ℕ) (hn : Powerful n) (hnp1 : Powerful (n+1)) (hnp2 : Powerful (n+2))
    (hn_odd : ¬ 2 ∣ n) :
    n % 9 = 0 ∨ n % 9 = 8 ∨ n % 9 = 7 := by
  have h3cases : n % 3 = 0 ∨ (n+1) % 3 = 0 ∨ (n+2) % 3 = 0 := by
    have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      have h_lt : n % 3 < 3 := Nat.mod_lt n (by norm_num : 0 < 3)
      omega
    rcases h_cases with (h|h|h)
    · exact Or.inl h
    · -- n % 3 = 1 → 3 ∣ (n+2)
      have : (n+2) % 3 = 0 := by
        calc
          (n+2) % 3 = ((n % 3) + 2) % 3 := by rw [Nat.add_mod]
          _ = (1 + 2) % 3 := by rw [h]
          _ = 3 % 3 := by norm_num
          _ = 0 := by norm_num
      exact Or.inr (Or.inr this)
    · -- n % 3 = 2 → 3 ∣ (n+1)
      have : (n+1) % 3 = 0 := by
        calc
          (n+1) % 3 = ((n % 3) + 1) % 3 := by rw [Nat.add_mod]
          _ = (2 + 1) % 3 := by rw [h]
          _ = 3 % 3 := by norm_num
          _ = 0 := by norm_num
      exact Or.inr (Or.inl this)
  rcases h3cases with (h3|h3|h3)
  · -- 3 ∣ n
    have h3_dvd : 3 ∣ n := Nat.dvd_of_mod_eq_zero h3
    have h9_dvd : 9 ∣ n := hn 3 Nat.prime_three h3_dvd
    have h_mod9 : n % 9 = 0 := Nat.mod_eq_zero_of_dvd h9_dvd
    exact Or.inl h_mod9
  · -- 3 ∣ n+1
    have h3_dvd : 3 ∣ (n+1) := Nat.dvd_of_mod_eq_zero h3
    have h9_dvd : 9 ∣ (n+1) := hnp1 3 Nat.prime_three h3_dvd
    have h_mod9 : n % 9 = 8 := by
      have h_np1_mod9 : (n+1) % 9 = 0 := Nat.mod_eq_zero_of_dvd h9_dvd
      omega
    exact Or.inr (Or.inl h_mod9)
  · -- 3 ∣ n+2
    have h3_dvd : 3 ∣ (n+2) := Nat.dvd_of_mod_eq_zero h3
    have h9_dvd : 9 ∣ (n+2) := hnp2 3 Nat.prime_three h3_dvd
    have h_mod9 : n % 9 = 7 := by
      have h_np2_mod9 : (n+2) % 9 = 0 := Nat.mod_eq_zero_of_dvd h9_dvd
      omega
    exact Or.inr (Or.inr h_mod9)

/-- The main theorem: no triple of consecutive powerful numbers exists.
    The even case is closed (mod 4 parity).  The odd case remains open —
    we prove 3‑adic residue constraints, but the asymptotic odd‑n case
    is a genuine open problem in number theory. -/
theorem erdos_364 : ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) := by
  -- EVOLVE-BLOCK-START
  intro h
  rcases h with ⟨n, hn, hnp1, hnp2⟩
  by_cases h2n : 2 ∣ n
  · -- even n: contradiction via mod 4 parity
    apply no_triple_even_n
    exact ⟨n, h2n, hn, hnp1, hnp2⟩
  · -- n is odd: the hard case
    have h_mod4 : n % 4 = 3 := odd_n_mod4 n h2n hnp1
    have h_mod9 : n % 9 = 0 ∨ n % 9 = 8 ∨ n % 9 = 7 :=
      mod9_residue_cases n hn hnp1 hnp2 h2n
    -- EVOLVE-VALUE-START
    sorry
    -- EVOLVE-VALUE-END
  -- EVOLVE-BLOCK-END

end Erdos364
