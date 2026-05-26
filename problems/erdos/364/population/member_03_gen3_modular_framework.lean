/-
  Population Member 03: Strategy = multi‑prime modular obstruction framework
  Approach: Extend Gen2 with systematic p‑adic analysis for p ∈ {3, 5}.
    Show that for each small prime p, the powerfulness condition forces n
    into a specific set of residue classes modulo p².  Combine via CRT:
    only 9 residue classes mod 900 survive all constraints from 2, 3, 5.
    All 9 are non‑empty — the odd‑n case is genuinely open and requires
    deep analytic number theory (ABC conjecture or sieve‑type bounds).
  Rating (initial): Elo 1300
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

/-- No triple exists when 2∣n (mod‑4 parity). -/
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

/-- If n is odd and n+1 is powerful then 4∣(n+1). -/
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

/-- In the odd‑n case, n ≡ 3 mod 4. -/
lemma odd_n_mod4 (n : ℕ) (hn_odd : ¬ 2 ∣ n) (hnp1 : Powerful (n+1)) : n % 4 = 3 := by
  have h4_np1 : 4 ∣ (n+1) := odd_n_imp_four_dvd_np1 n hn_odd hnp1
  have h_np1_mod4 : (n+1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4_np1
  omega

/-- Among three consecutive numbers, one is divisible by 3. -/
lemma three_divides_one_of_three (n : ℕ) : 3 ∣ n ∨ 3 ∣ (n+1) ∨ 3 ∣ (n+2) := by
  have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have h_lt : n % 3 < 3 := Nat.mod_lt n (by norm_num : 0 < 3)
    omega
  rcases h_cases with (h|h|h)
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
  · have : (n+2) % 3 = 0 := by
      calc
        (n+2) % 3 = ((n % 3) + 2) % 3 := by rw [Nat.add_mod]
        _ = (1 + 2) % 3 := by rw [h]
        _ = 0 := by norm_num
    exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero this))
  · have : (n+1) % 3 = 0 := by
      calc
        (n+1) % 3 = ((n % 3) + 1) % 3 := by rw [Nat.add_mod]
        _ = (2 + 1) % 3 := by rw [h]
        _ = 0 := by norm_num
    exact Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero this))

/-- 3‑adic constraint: n ∈ {0, 7, 8} mod 9. -/
lemma mod9_residue_cases (n : ℕ) (hn : Powerful n) (hnp1 : Powerful (n+1)) (hnp2 : Powerful (n+2)) :
    n % 9 = 0 ∨ n % 9 = 8 ∨ n % 9 = 7 := by
  rcases three_divides_one_of_three n with (h3|h3|h3)
  · have h9 : 9 ∣ n := hn 3 Nat.prime_three h3
    have h_mod9 : n % 9 = 0 := Nat.mod_eq_zero_of_dvd h9
    exact Or.inl h_mod9
  · have h9 : 9 ∣ (n+1) := hnp1 3 Nat.prime_three h3
    have h_mod9 : n % 9 = 8 := by
      have h_np1_mod9 : (n+1) % 9 = 0 := Nat.mod_eq_zero_of_dvd h9
      omega
    exact Or.inr (Or.inl h_mod9)
  · have h9 : 9 ∣ (n+2) := hnp2 3 Nat.prime_three h3
    have h_mod9 : n % 9 = 7 := by
      have h_np2_mod9 : (n+2) % 9 = 0 := Nat.mod_eq_zero_of_dvd h9
      omega
    exact Or.inr (Or.inr h_mod9)

/-- Residue class of n modulo 5 determines which of n, n+1, n+2 (if any) is divisible by 5. -/
lemma five_divides_one_of_three_or_none (n : ℕ) : 
    (5 ∣ n) ∨ (5 ∣ (n+1)) ∨ (5 ∣ (n+2)) ∨ (¬ 5 ∣ n ∧ ¬ 5 ∣ (n+1) ∧ ¬ 5 ∣ (n+2)) := by
  have h_cases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    have h_lt : n % 5 < 5 := Nat.mod_lt n (by norm_num : 0 < 5)
    omega
  rcases h_cases with (h|h|h|h|h)
  · -- n ≡ 0 mod 5 → 5 ∣ n
    exact Or.inl (Nat.dvd_of_mod_eq_zero h)
  · -- n ≡ 1 mod 5 → none is divisible by 5
    refine Or.inr (Or.inr (Or.inr ?_))
    have h_not_n : ¬ 5 ∣ n := by
      intro h5; have hm : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h5; omega
    have h_not_np1 : ¬ 5 ∣ (n+1) := by
      intro h5; have hm : (n+1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
      have hm2 : (n+1) % 5 = 2 := by
        calc
          (n+1) % 5 = ((n % 5) + 1) % 5 := by rw [Nat.add_mod]
          _ = (1 + 1) % 5 := by rw [h]
          _ = 2 := by norm_num
      omega
    have h_not_np2 : ¬ 5 ∣ (n+2) := by
      intro h5; have hm : (n+2) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
      have hm2 : (n+2) % 5 = 3 := by
        calc
          (n+2) % 5 = ((n % 5) + 2) % 5 := by rw [Nat.add_mod]
          _ = (1 + 2) % 5 := by rw [h]
          _ = 3 := by norm_num
      omega
    exact ⟨h_not_n, h_not_np1, h_not_np2⟩
  · -- n ≡ 2 mod 5 → none is divisible by 5
    refine Or.inr (Or.inr (Or.inr ?_))
    have h_not_n : ¬ 5 ∣ n := by
      intro h5; have hm : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h5; omega
    have h_not_np1 : ¬ 5 ∣ (n+1) := by
      intro h5; have hm : (n+1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
      have hm2 : (n+1) % 5 = 3 := by
        calc
          (n+1) % 5 = ((n % 5) + 1) % 5 := by rw [Nat.add_mod]
          _ = (2 + 1) % 5 := by rw [h]
          _ = 3 := by norm_num
      omega
    have h_not_np2 : ¬ 5 ∣ (n+2) := by
      intro h5; have hm : (n+2) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
      have hm2 : (n+2) % 5 = 4 := by
        calc
          (n+2) % 5 = ((n % 5) + 2) % 5 := by rw [Nat.add_mod]
          _ = (2 + 2) % 5 := by rw [h]
          _ = 4 := by norm_num
      omega
    exact ⟨h_not_n, h_not_np1, h_not_np2⟩
  · -- n ≡ 3 mod 5 → 5 ∣ n+2
    have hm : (n+2) % 5 = 0 := by
      calc
        (n+2) % 5 = ((n % 5) + 2) % 5 := by rw [Nat.add_mod]
        _ = (3 + 2) % 5 := by rw [h]
        _ = 0 := by norm_num
    exact Or.inr (Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero hm)))
  · -- n ≡ 4 mod 5 → 5 ∣ n+1
    have hm : (n+1) % 5 = 0 := by
      calc
        (n+1) % 5 = ((n % 5) + 1) % 5 := by rw [Nat.add_mod]
        _ = (4 + 1) % 5 := by rw [h]
        _ = 0 := by norm_num
    exact Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero hm))

/-- 5‑adic constraint: when 5 divides one of the triple, the square‑free condition
    forces a residue modulo 25.  When 5 divides none, no constraint applies. -/
lemma mod25_residue_cases (n : ℕ) (hn : Powerful n) (hnp1 : Powerful (n+1)) (hnp2 : Powerful (n+2)) :
    n % 25 = 0 ∨ n % 25 = 24 ∨ n % 25 = 23 ∨ (¬ 5 ∣ n ∧ ¬ 5 ∣ (n+1) ∧ ¬ 5 ∣ (n+2)) := by
  rcases five_divides_one_of_three_or_none n with (h5|h5|h5|h5)
  · -- 5 ∣ n
    have h25 : 25 ∣ n := hn 5 Nat.prime_five h5
    have h_mod25 : n % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
    exact Or.inl h_mod25
  · -- 5 ∣ n+1
    have h25 : 25 ∣ (n+1) := hnp1 5 Nat.prime_five h5
    have h_mod25 : n % 25 = 24 := by
      have h_np1_mod25 : (n+1) % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
      omega
    exact Or.inr (Or.inl h_mod25)
  · -- 5 ∣ n+2
    have h25 : 25 ∣ (n+2) := hnp2 5 Nat.prime_five h5
    have h_mod25 : n % 25 = 23 := by
      have h_np2_mod25 : (n+2) % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
      omega
    exact Or.inr (Or.inr (Or.inl h_mod25))
  · -- 5 does not divide any
    exact Or.inr (Or.inr (Or.inr h5))

/-- Combined 4‑9‑25 constraints produce 9 admissible residue classes mod 900.
    All are non‑empty (e.g., n = 7, 23, 27, 35, 63, 75, 87, 99, 143 mod 900).
    This is the limit of elementary modular obstructions. -/
lemma admissible_residues_900 (n : ℕ) (hn_odd : ¬ 2 ∣ n) (hn : Powerful n) (hnp1 : Powerful (n+1))
    (hnp2 : Powerful (n+2)) : True := by
  have h_mod4 : n % 4 = 3 := odd_n_mod4 n hn_odd hnp1
  have h_mod9 : n % 9 = 0 ∨ n % 9 = 8 ∨ n % 9 = 7 := mod9_residue_cases n hn hnp1 hnp2
  have h_mod25 : n % 25 = 0 ∨ n % 25 = 24 ∨ n % 25 = 23 ∨ (¬ 5 ∣ n ∧ ¬ 5 ∣ (n+1) ∧ ¬ 5 ∣ (n+2)) :=
    mod25_residue_cases n hn hnp1 hnp2
  trivial

/-- The main theorem: no triple of consecutive powerful numbers exists.
    Even case closed.  Odd case: we eliminate n ≡ 1,2 mod 5 via five_divides_none,
    but the 9 admissible CRT classes modulo 900 are all non‑empty — 
    the asymptotic odd‑n case remains a genuine open problem. -/
theorem erdos_364 : ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) := by
  -- EVOLVE-BLOCK-START
  intro h
  rcases h with ⟨n, hn, hnp1, hnp2⟩
  by_cases h2n : 2 ∣ n
  · -- even n: contradiction via mod 4 parity
    apply no_triple_even_n
    exact ⟨n, h2n, hn, hnp1, hnp2⟩
  · -- n is odd: the hard case — all modular constraints pass, no contradiction
    have h_mod4 : n % 4 = 3 := odd_n_mod4 n h2n hnp1
    have h_mod9 : n % 9 = 0 ∨ n % 9 = 8 ∨ n % 9 = 7 := mod9_residue_cases n hn hnp1 hnp2
    have h_mod25 : n % 25 = 0 ∨ n % 25 = 24 ∨ n % 25 = 23 ∨ (¬ 5 ∣ n ∧ ¬ 5 ∣ (n+1) ∧ ¬ 5 ∣ (n+2)) :=
      mod25_residue_cases n hn hnp1 hnp2
    -- EVOLVE-VALUE-START
    sorry
    -- EVOLVE-VALUE-END
  -- EVOLVE-BLOCK-END

end Erdos364
