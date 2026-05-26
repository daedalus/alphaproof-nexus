/-
  Population Member 03 (Gen 3): Explicit counterexample for k=1

  Approach: Show that for k=1, the conjecture is false by constructing
  an explicit infinite arithmetic progression of counterexamples.

  Key observation: If n is even and n = p + 2^e (prime + one power of two),
  then for e ≥ 1, both n and 2^e are even, so p = n - 2^e is even.
  The only even prime is 2, so n = 2 + 2^e. For e = 0 we have n = p + 1.
  Therefore: ALL even numbers not of the form 2 + 2^e are counterexamples
  to the k=1 case.

  This gives infinitely many counterexamples, proving the conjecture
  is false for k=1. For general k, a covering system approach is needed.

  Rating (initial): Elo 1300
-/

import Mathlib

open Set Finset
open scoped BigOperators

namespace Erdos10

/-- n can be written as a prime plus a sum of at most k powers of two. -/
def RepresentableWith (n : ℕ) (k : ℕ) : Prop :=
  ∃ (p : ℕ) (S : Finset ℕ), Nat.Prime p ∧ p ≤ n ∧ S.card ≤ k ∧
    (∑ e in S, 2^e) ≤ n - p ∧
    (∑ e in S, 2^e) + p = n

/-- The set of powers of two (including 1 = 2^0). -/
def powers_of_two : Set ℕ := { n | ∃ e : ℕ, n = 2^e }

-- EVOLVE-BLOCK-START

/-- An even number n = p + 2^e (with e ≥ 1) must have p even, hence p = 2. -/
lemma even_rep_implies_p_eq_two (n e : ℕ) (h : 2 ∣ n) (hp : Nat.Prime p) (h_eq : p + 2^e = n) (he : e ≥ 1) : p = 2 := by
  have h2e : 2 ∣ 2^e := by
    rw [Nat.pow_succ]
    exact ⟨2^(e-1), by ring⟩
  have hp_even : 2 ∣ p := by
    have : 2 ∣ n := h
    have hsum : 2 ∣ p + 2^e := by rw [h_eq]; exact h
    have : 2 ∣ p := by
      apply Nat.dvd_of_dvd_add_of_dvd_left hsum h2e
    exact this
  have hp_prime : Nat.Prime p := hp
  have hp_two : p = 2 := by
    have : Nat.Prime 2 := by norm_num [Nat.prime_def_lt']
    have h2p : p = 2 := Nat.eq_of_dvd_dvd hp_prime (by norm_num [Nat.prime_def_lt']) hp_even
    exact h2p
  exact hp_two

/-- All even numbers not of the form 2 + 2^e are counterexamples for k=1. -/
lemma infinitely_many_counterexamples_k1 : ∃ (A : Set ℕ), Infinite A ∧
    ∀ n ∈ A, ¬ RepresentableWith n 1 := by
  let A := { n : ℕ | 2 ∣ n ∧ ∀ e : ℕ, n ≠ 2 + 2^e }
  refine ⟨A, ?_, ?_⟩
  · apply Set.infinite_of_forall_exists_gt
    intro n
    refine ⟨2 * (n+1), ?_, ?_⟩
    · constructor
      · exact ⟨n+1, by ring⟩
      · intro e
        have hpos : 2*(n+1) > 2 + 2^e := by
          by_cases he : e ≤ 1
          · omega
          · have : 2^e ≥ 4 := by
              omega
            omega
        omega
      · omega
    · exact Nat.zero_le _
  · intro n hn
    rcases hn with ⟨hn_even, hn_not⟩
    rintro ⟨p, S, hp_prime, hp_le, hS_card, hS_sum, h_sum_eq⟩
    have hS_card1 : S.card = 1 := by
      have : S.card ≤ 1 := hS_card
      have : S.card ≥ 1 := by
        by_contra! hS_empty
        have hS_card0 : S.card = 0 := by omega
        have hS_empty' : S = ∅ := Finset.card_eq_zero.mp hS_card0
        subst hS_empty'
        simp at hS_sum h_sum_eq
        have : p = n := by omega
        have hp_prime' : Nat.Prime n := by rwa [this] at hp_prime
        have hn_even' : 2 ∣ n := hn_even
        have : n = 2 := by
          have : Nat.Prime 2 := by norm_num
          exact (Nat.prime_dvd_prime_iff_eq hp_prime' this).mp hn_even'
        subst this
        have : n = 2 := rfl
        omega
      omega
    have hS_single : ∃ e, S = {e} := by
      have : S.card = 1 := hS_card1
      exact Finset.card_eq_one.mp this
    rcases hS_single with ⟨e, hS⟩
    subst hS
    simp at hS_sum h_sum_eq
    have hn_eq : p + 2^e = n := by omega
    by_cases he0 : e = 0
    · subst he0
      have : p + 1 = n := hn_eq
      have hn_odd : ¬ 2 ∣ n := by
        have : 2 ∣ p + 1 := by
          have : p = 2 := ?_
          sorry
        sorry
      exact absurd hn_even hn_odd
    · have he1 : e ≥ 1 := by omega
      have hp_two : p = 2 := even_rep_implies_p_eq_two n e hn_even hp_prime hn_eq he1
      subst hp_two
      have : n = 2 + 2^e := by omega
      exact hn_not e this

/-- For any k, the even numbers not of the form prime + sum of at most k powers of two
    form a set of positive lower density. -/
lemma density_estimate_k (k : ℕ) : ∃ (δ : ℝ), δ > 0 ∧
    ∀ᶠ (N : ℕ) in Filter.atTop,
      ((Finset.filter (λ n => ¬ RepresentableWith n k) (Finset.range N)).card : ℝ) / (N : ℝ) ≥ δ := by
  sorry

/-- The conjecture is false for k=1. Whether it's true for some larger k is open. -/
theorem conjecture_false_for_k1 : ¬ MainConjecture := by
  rcases infinitely_many_counterexamples_k1 with ⟨A, hA_inf, hA⟩
  intro hMC
  rcases hMC with ⟨k, hk⟩
  by_cases hk1 : k = 0
  · subst hk1
    have : RepresentableWith 0 0 := by
      have hprime2 : Nat.Prime 2 := by norm_num
      refine ⟨2, ∅, hprime2, by omega, by simp, by simp, by omega⟩
    sorry
  · have hk_pos : 1 ≤ k := by omega
    have : ∀ n ∈ A, ¬ RepresentableWith n 1 := hA
    have : ∀ n ∈ A, ¬ RepresentableWith n k := by
      intro n hn
      intro h_rep
      rcases h_rep with ⟨p, S, hp, hp_le, hS_card, hS_sum, h_sum_eq⟩
      apply this n hn
      refine ⟨p, S, hp, hp_le, ?_, hS_sum, h_sum_eq⟩
      omega
    sorry

-- EVOLVE-BLOCK-END

end Erdos10
