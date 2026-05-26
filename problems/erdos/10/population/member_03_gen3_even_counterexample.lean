/-
  Population Member 03 (Gen 3): Explicit counterexample for k=1

  Approach: Show that for k=1, the conjecture is false by constructing
  an explicit infinite set of counterexamples.

  Key observation: for k=1, an even n can be written as p + 2^e (e≥0) or
  as p itself (the S=∅ case).
  - S=∅: n = p, so n must be prime. Only n=2 works.
  - e=0: n = p + 1, so n-1 must be prime.
  - e≥1: n = p + 2^e. Both n and 2^e are even → p even → p=2 → n = 2+2^e.

  Therefore any even n with n-1 composite and n-2 not a power of 2
  is a counterexample. The set of such n is infinite.

  Rating (initial): Elo 1300
-/

import Mathlib

open Set Finset
open scoped BigOperators

namespace Erdos10

/-- n can be written as a prime plus a sum of at most k powers of two. -/
def RepresentableWith (n : ℕ) (k : ℕ) : Prop :=
  ∃ (p : ℕ) (S : Finset ℕ), Nat.Prime p ∧ p ≤ n ∧ S.card ≤ k ∧
    (∑ e ∈ S, 2^e) + p = n

/-- The main conjecture: there exists k such that every sufficiently large
    integer n is representable with at most k powers of two. -/
def MainConjecture : Prop :=
  ∃ (k : ℕ), Filter.Eventually (RepresentableWith · k) Filter.atTop

/-- If n is even and n = p + 2^e with e ≥ 1, then p = 2. -/
lemma even_rep_with_power_implies_two (n e : ℕ) (p : ℕ) (hn_even : 2 ∣ n) (hp_prime : Nat.Prime p)
    (h_eq : p + 2^e = n) (he : e ≥ 1) : p = 2 := by
  have h2e_even : 2 ∣ 2^e := by
    refine ⟨2^(e-1), ?_⟩
    calc
      2^e = 2^((e-1)+1) := by rw [Nat.sub_add_cancel he]
      _ = 2^(e-1) * 2 := by rw [Nat.pow_succ]
      _ = 2 * 2^(e-1) := mul_comm _ _
  have hsum : 2 ∣ p + 2^e := by
    rw [h_eq]
    exact hn_even
  have hsum' : 2 ∣ 2^e + p := by simpa [add_comm] using hsum
  have hp_even : 2 ∣ p := (Nat.dvd_add_iff_right h2e_even).mpr hsum'
  have h2_prime : Nat.Prime 2 := by norm_num
  rcases hp_prime.eq_one_or_self_of_dvd 2 hp_even with (h | h)
  · linarith
  · exact h.symm

-- EVOLVE-BLOCK-START

/-- Even numbers n such that n-1 is composite and n-2 is not a power of 2
    are NOT representable for k=1. -/
lemma not_representable_even_counterexample (n : ℕ) (hn_even : 2 ∣ n) (hn_composite : ¬ Nat.Prime (n-1))
    (hn_not_pow2 : ∀ e, n - 2 ≠ 2^e) (hn_not_two : n ≠ 2) : ¬ RepresentableWith n 1 := by
  intro h
  rcases h with ⟨p, S, hp_prime, hp_le, hS_card, h_sum_eq⟩
  by_cases hS_empty : S = ∅
  · subst hS_empty
    simp at h_sum_eq
    have : n = p := by omega
    subst this
    have h2_prime : Nat.Prime 2 := by norm_num
    rcases hp_prime.eq_one_or_self_of_dvd 2 hn_even with (h | h)
    · linarith
    · exact hn_not_two h.symm
  · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hS_card1 : S.card = 1 := by
      have : 1 ≤ S.card := Finset.one_le_card.mpr hS_nonempty
      have : S.card ≤ 1 := hS_card
      omega
    rcases Finset.card_eq_one.mp hS_card1 with ⟨e, hS⟩
    subst hS
    simp at h_sum_eq
    have hn_eq : p + 2^e = n := by omega
    by_cases he0 : e = 0
    · subst he0
      have : p + 1 = n := hn_eq
      have : p = n - 1 := by omega
      subst this
      exact hn_composite hp_prime
    · have he1 : e ≥ 1 := by omega
      have hp_two : p = 2 := even_rep_with_power_implies_two n e p hn_even hp_prime hn_eq he1
      subst hp_two
      have : n - 2 = 2^e := by omega
      exact hn_not_pow2 e this

/-- There are infinitely many counterexamples to the k=1 case.

    Construction: n = 28 + 36·t for t ∈ ℕ.
    - n is even: n = 2·(14 + 18·t)
    - n - 1 = 27 + 36·t = 9·(3 + 4·t) is divisible by 9 and > 9 for all t, hence composite
    - n - 2 = 26 + 36·t = 2·(13 + 18·t). For e ≥ 2, 2^e ≡ 0 (mod 4) but n-2 ≡ 2 (mod 4)
      because 13+18t is odd. For e=0,1, 2^e ∈ {1,2} and n-2 ≥ 26. So never a power of 2.
    - n ≠ 2
-/
lemma infinitely_many_counterexamples_k1 : ∃ (A : Set ℕ), Set.Infinite A ∧
    ∀ n ∈ A, ¬ RepresentableWith n 1 := by
  let A := { n : ℕ | ∃ t : ℕ, n = 28 + 36*t }
  have hA_inf : Set.Infinite A := by
    have h_inj : Function.Injective (λ (t : ℕ) => 28 + 36*t) := by
      intro x y h
      have h' : 28 + 36*x = 28 + 36*y := h
      omega
    have h_range_subset : Set.range (λ (t : ℕ) => 28 + 36*t) ⊆ A := by
      rintro n ⟨t, rfl⟩; exact ⟨t, rfl⟩
    have h_range_infinite : Set.Infinite (Set.range (λ (t : ℕ) => 28 + 36*t)) :=
      Set.infinite_range_of_injective h_inj
    exact Set.Infinite.mono h_range_subset h_range_infinite
  have hA_not_rep : ∀ n ∈ A, ¬ RepresentableWith n 1 := by
    intro n hn
    rcases hn with ⟨t, hn_eq⟩
    subst hn_eq
    have hn_even : 2 ∣ 28 + 36*t := by
      use 14 + 18*t
      ring
    have hn_not_two : 28 + 36*t ≠ 2 := by omega
    have hn_comp : ¬ Nat.Prime (28 + 36*t - 1) := by
      have : 28 + 36*t - 1 = 27 + 36*t := by omega
      rw [this]
      have h9_ne1 : (9 : ℕ) ≠ 1 := by norm_num
      have h_factor_ne1 : (3 + 4*t : ℕ) ≠ 1 := by omega
      have h_mul : 9 * (3 + 4*t) = 27 + 36*t := by ring
      have h_eq : 27 + 36*t = 9 * (3 + 4*t) := by omega
      rw [h_eq]
      exact Nat.not_prime_mul h9_ne1 h_factor_ne1
    have hn_pow2 : ∀ e : ℕ, 28 + 36*t - 2 ≠ 2^e := by
      intro e
      have : 28 + 36*t - 2 = 26 + 36*t := by omega
      rw [this]
      by_cases he0 : e = 0
      · subst he0; omega
      by_cases he1 : e = 1
      · subst he1; omega
      have he2 : 2 ≤ e := by omega
      have hpow_mod4 : 2^e % 4 = 0 := by
        have h4 : 4 ∣ 2^e := by
          have : 2^2 = 4 := by norm_num
          have h4pow : 2^2 ∣ 2^e := pow_dvd_pow 2 he2
          simpa [this] using h4pow
        exact Nat.mod_eq_zero_of_dvd h4
      have hn_mod4 : (26 + 36*t) % 4 = 2 := by
        calc
          (26 + 36*t) % 4 = ((26 % 4) + (36*t % 4)) % 4 := by rw [Nat.add_mod]
          _ = (2 + 0) % 4 := by
            simp [show 36*t % 4 = 0 from by
              have : 4 ∣ 36*t := ⟨9*t, by ring⟩
              exact Nat.mod_eq_zero_of_dvd this]
          _ = 2 := by norm_num
      intro h
      have : 2^e % 4 = (26 + 36*t) % 4 := by rw [h]
      rw [hpow_mod4, hn_mod4] at this
      norm_num at this
    exact not_representable_even_counterexample (28 + 36*t) hn_even hn_comp hn_pow2 hn_not_two
  exact ⟨A, hA_inf, hA_not_rep⟩

/-- The conjecture is false for k=1: there exist infinitely many n
    not representable with at most 1 power of two, so ¬(Eventually representable). -/
theorem conjecture_false_for_k1 : ¬ Filter.Eventually (RepresentableWith · 1) Filter.atTop := by
  rcases infinitely_many_counterexamples_k1 with ⟨A, hA_inf, hA⟩
  intro h
  rcases Filter.eventually_atTop.mp h with ⟨M, hM⟩
  have h_exists_gt : ∃ n ∈ A, M < n := by
    by_contra h_not
    have h_all : ∀ n, n ∈ A → n ≤ M := by
      intro n hn
      by_contra! h_gt
      apply h_not
      exact ⟨n, hn, h_gt⟩
    have h_bdd : Set.Finite A := by
      have h_sub : A ⊆ (Finset.range (M+1) : Set ℕ) := by
        intro n hn
        have hn_le_M : n ≤ M := h_all n hn
        have : n < M+1 := by omega
        simpa
      exact Set.Finite.subset (Finset.finite_toSet _) h_sub
    exact hA_inf h_bdd
  rcases h_exists_gt with ⟨n, hnA, hn_gt⟩
  have hrep_n : RepresentableWith n 1 := hM n (le_of_lt hn_gt)
  exact hA n hnA hrep_n

-- EVOLVE-BLOCK-END

end Erdos10
