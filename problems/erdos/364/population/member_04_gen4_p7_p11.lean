/-
  Population Member 04 (Gen 4): Strategy = 7‑adic and 11‑adic modular obstruction

  Approach: Extend Gen3 (2,3,5‑adic) with p=7 and p=11 analysis.
  For p=7:
    - Among n, n+1, n+2, one is ≡ 0,1,2,3,4,5,6 mod 7.
    - If p∣n+k for k∈{0,1,2}, then 49∣n+k by powerfulness.
    - Solve n ≡ -k (mod 49) and combine with n ≡ 3 (mod 4) from mod‑4 analysis.
  For p=11:
    - Similar analysis with 121 dividing the appropriate term.
  Combine via CRT: 4×9×25×49×121 = 5,346,900.
  Narrow from 9 admissible classes to hopefully 0, proving the odd case.

  Rating (initial): Elo 1350
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

lemma five_divides_one_of_three_or_none (n : ℕ) :
    (5 ∣ n) ∨ (5 ∣ (n+1)) ∨ (5 ∣ (n+2)) ∨ (¬ 5 ∣ n ∧ ¬ 5 ∣ (n+1) ∧ ¬ 5 ∣ (n+2)) := by
  have h_cases : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    have h_lt : n % 5 < 5 := Nat.mod_lt n (by norm_num : 0 < 5)
    omega
  rcases h_cases with (h|h|h|h|h)
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
  · refine Or.inr (Or.inr (Or.inr ?_))
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
  · refine Or.inr (Or.inr (Or.inr ?_))
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

/-- 5‑adic constraint. -/
lemma mod25_residue_cases (n : ℕ) (hn : Powerful n) (hnp1 : Powerful (n+1)) (hnp2 : Powerful (n+2)) :
    n % 25 = 0 ∨ n % 25 = 24 ∨ n % 25 = 23 ∨ (¬ 5 ∣ n ∧ ¬ 5 ∣ (n+1) ∧ ¬ 5 ∣ (n+2)) := by
  rcases five_divides_one_of_three_or_none n with (h5|h5|h5|h5)
  · have h25 : 25 ∣ n := hn 5 Nat.prime_five h5
    have h_mod25 : n % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
    exact Or.inl h_mod25
  · have h25 : 25 ∣ (n+1) := hnp1 5 Nat.prime_five h5
    have h_mod25 : n % 25 = 24 := by
      have h_np1_mod25 : (n+1) % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
      omega
    exact Or.inr (Or.inl h_mod25)
  · have h25 : 25 ∣ (n+2) := hnp2 5 Nat.prime_five h5
    have h_mod25 : n % 25 = 23 := by
      have h_np2_mod25 : (n+2) % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
      omega
    exact Or.inr (Or.inr (Or.inl h_mod25))
  · exact Or.inr (Or.inr (Or.inr h5))

/-- Among n, n+1, n+2, one is divisible by 7. -/
lemma seven_divides_one_of_three (n : ℕ) : 7 ∣ n ∨ 7 ∣ (n+1) ∨ 7 ∣ (n+2) := by
  have h_cases : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
    have h_lt : n % 7 < 7 := Nat.mod_lt n (by norm_num : 0 < 7)
    omega
  rcases h_cases with (h|h|h|h|h|h|h)
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
  · have hm : (n+6) % 7 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+5) % 7 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+4) % 7 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+3) % 7 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+2) % 7 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+1) % 7 = 0 := by omega; exact Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero hm))

/-- 7‑adic constraint: when 7 divides one of the triple, 49 must also divide it. -/
lemma mod49_residue_cases (n : ℕ) (hn : Powerful n) (hnp1 : Powerful (n+1)) (hnp2 : Powerful (n+2)) :
    n % 49 = 0 ∨ n % 49 = 48 ∨ n % 49 = 47 := by
  rcases seven_divides_one_of_three n with (h7|h7|h7)
  · have h49 : 49 ∣ n := hn 7 Nat.prime_seven h7
    have h_mod49 : n % 49 = 0 := Nat.mod_eq_zero_of_dvd h49
    exact Or.inl h_mod49
  · have h49 : 49 ∣ (n+1) := hnp1 7 Nat.prime_seven h7
    have h_mod49 : n % 49 = 48 := by
      have h_np1_mod49 : (n+1) % 49 = 0 := Nat.mod_eq_zero_of_dvd h49
      omega
    exact Or.inr (Or.inl h_mod49)
  · have h49 : 49 ∣ (n+2) := hnp2 7 Nat.prime_seven h7
    have h_mod49 : n % 49 = 47 := by
      have h_np2_mod49 : (n+2) % 49 = 0 := Nat.mod_eq_zero_of_dvd h49
      omega
    exact Or.inr (Or.inr h_mod49)

/-- Among n, n+1, n+2, one is divisible by 11. -/
lemma eleven_divides_one_of_three (n : ℕ) : 11 ∣ n ∨ 11 ∣ (n+1) ∨ 11 ∣ (n+2) := by
  have h_cases : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨
    n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
    have h_lt : n % 11 < 11 := Nat.mod_lt n (by norm_num : 0 < 11)
    omega
  rcases h_cases with (h|h|h|h|h|h|h|h|h|h|h)
  · exact Or.inl (Nat.dvd_of_mod_eq_zero h)
  · have hm : (n+10) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+9) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+8) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+7) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+6) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+5) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+4) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+3) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+2) % 11 = 0 := by omega; exact Or.inr (Or.inr (Nat.dvd_of_mod_eq_zero hm))
  · have hm : (n+1) % 11 = 0 := by omega; exact Or.inr (Or.inl (Nat.dvd_of_mod_eq_zero hm))

/-- 11‑adic constraint: when 11 divides one of the triple, 121 must also divide it. -/
lemma mod121_residue_cases (n : ℕ) (hn : Powerful n) (hnp1 : Powerful (n+1)) (hnp2 : Powerful (n+2)) :
    n % 121 = 0 ∨ n % 121 = 120 ∨ n % 121 = 119 := by
  rcases eleven_divides_one_of_three n with (h11|h11|h11)
  · have h121 : 121 ∣ n := hn 11 (by exact Nat.prime_11) h11
    have h_mod121 : n % 121 = 0 := Nat.mod_eq_zero_of_dvd h121
    exact Or.inl h_mod121
  · have h121 : 121 ∣ (n+1) := hnp1 11 (by exact Nat.prime_11) h11
    have h_mod121 : n % 121 = 120 := by
      have h_np1_mod121 : (n+1) % 121 = 0 := Nat.mod_eq_zero_of_dvd h121
      omega
    exact Or.inr (Or.inl h_mod121)
  · have h121 : 121 ∣ (n+2) := hnp2 11 (by exact Nat.prime_11) h11
    have h_mod121 : n % 121 = 119 := by
      have h_np2_mod121 : (n+2) % 121 = 0 := Nat.mod_eq_zero_of_dvd h121
      omega
    exact Or.inr (Or.inr h_mod121)

-- EVOLVE-BLOCK-START

/-- Combined 4-9-25-49-121 constraints.
    The modulus is 4·9·25·49·121 = 5,346,900.
    CRT eliminates some of the 9 admissible residues from Gen3.
    If all are eliminated, the odd case is closed. -/
lemma combined_modular_obstruction (n : ℕ) (h2n : ¬ 2 ∣ n) (hn : Powerful n) (hnp1 : Powerful (n+1)) (hnp2 : Powerful (n+2)) :
    False := by
  have h_mod4 : n % 4 = 3 := odd_n_mod4 n h2n hnp1
  have h_mod9 : n % 9 = 0 ∨ n % 9 = 8 ∨ n % 9 = 7 := mod9_residue_cases n hn hnp1 hnp2
  have h_mod25 : n % 25 = 0 ∨ n % 25 = 24 ∨ n % 25 = 23 ∨ (¬ 5 ∣ n ∧ ¬ 5 ∣ (n+1) ∧ ¬ 5 ∣ (n+2)) :=
    mod25_residue_cases n hn hnp1 hnp2
  have h_mod49 : n % 49 = 0 ∨ n % 49 = 48 ∨ n % 49 = 47 := mod49_residue_cases n hn hnp1 hnp2
  have h_mod121 : n % 121 = 0 ∨ n % 121 = 120 ∨ n % 121 = 119 := mod121_residue_cases n hn hnp1 hnp2
  -- CRT over 4, 9, 25, 49, 121. Check if any residue satisfies all constraints.
  -- If none does, this is a contradiction.
  sorry

/-- The main theorem: no triple of consecutive powerful numbers exists. -/
theorem erdos_364 : ¬ ∃ (n : ℕ), Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2) := by
  intro h
  rcases h with ⟨n, hn, hnp1, hnp2⟩
  by_cases h2n : 2 ∣ n
  · apply no_triple_even_n; exact ⟨n, h2n, hn, hnp1, hnp2⟩
  · exact combined_modular_obstruction n h2n hn hnp1 hnp2

-- EVOLVE-BLOCK-END

end Erdos364
