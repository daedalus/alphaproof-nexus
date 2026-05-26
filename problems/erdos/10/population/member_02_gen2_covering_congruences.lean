/-
  Population Member 02 (Gen 2): Covering congruences and Romanov's theorem

  Approach:
  1. Define R_k(n) = number of representations of n as p + Σ_{i=1}^{k} 2^{e_i}
     (prime + sum of at most k powers of two).
  2. Show via sieve bounds that the set of integers not representable
     with k powers of two has upper density at most f(k) → 0.
  3. Use a covering congruence system (Erdős–Selfridge style) to show
     that if k is too small, the uncovered set has positive lower density.
  4. The gap between the upper bound (from sieve) and the lower bound
     (from covering) narrows as k grows. The conjecture asks whether
     there exists k where the lower bound vanishes.

  Key lemmas:
  - Romanov's theorem: |{n ≤ N : n = p + 2^k}| ~ c·N for some c > 0.
  - For a fixed k, |{n ≤ N : n = p + Σ_{i=1}^{k} 2^{e_i}}| ≤ C_k·N / log N.
  - Covering system: residues a_i mod m_i such that every large integer
    satisfies n ≡ a_i (mod m_i) for some i, and for each residue,
    some congruence blocks n - 2^{e} from being prime.

  Rating (initial): Elo 1250
-/

import Mathlib

open Set Finset
open scoped BigOperators Filter

namespace Erdos10

/-- n can be written as a prime plus a sum of at most k powers of two. -/
def RepresentableWith (n : ℕ) (k : ℕ) : Prop :=
  ∃ (p : ℕ) (S : Finset ℕ), Nat.Prime p ∧ p ≤ n ∧ S.card ≤ k ∧
    (∑ e ∈ S, 2^e) + p = n

/-- The main conjecture: there exists k such that every sufficiently large
    integer n is representable with at most k powers of two. -/
def MainConjecture : Prop :=
  ∃ (k : ℕ), Filter.Eventually (λ n => RepresentableWith n k) Filter.atTop

/-- The representation function: number of ways to write n as p + 2^e. -/
noncomputable def r (n : ℕ) : ℕ := by
  classical
  exact (Finset.filter (λ (p : ℕ) => Nat.Prime p ∧ ∃ (e : ℕ), p + 2^e = n)
    (Finset.range (n+1))).card

/-- The representation function for at most k powers of two. -/
noncomputable def r_k (n : ℕ) (k : ℕ) : ℕ := by
  classical
  exact (Finset.filter (λ (S : Finset ℕ) => S.card ≤ k ∧ (∃ p : ℕ, Nat.Prime p ∧ p + (∑ e ∈ S, 2^e) = n))
    (Finset.powerset (Finset.range n))).card

/-- For k=1, Romanov's theorem gives positive density. -/
lemma romanov_positive_density : ∃ (c : ℝ), c > 0 ∧
    Filter.Eventually (λ (N : ℕ) => ((by
        classical
        exact ((Finset.filter (λ n => r n ≥ 1) (Finset.range N)).card : ℝ)) / (N : ℝ) ≥ c)) Filter.atTop := by
  -- Romanov 1934: the set {p + 2^k} has positive lower density
  -- This is a deep analytic number theorem; we leave it as an assumption
  sorry

-- EVOLVE-BLOCK-START

/-- An upper bound on how many subsets S of size at most k exist whose sum
    with a prime reaches n. This is at most the number of subsets S of size
    at most k of {0..n-1}. -/
lemma r_k_upper_bound (n : ℕ) (k : ℕ) (hk : 0 < k) : r_k n k ≤ ((Finset.powerset (Finset.range n)).filter (λ S => S.card ≤ k)).card := by
  sorry

/-- If MainConjecture holds for some k, then the set of non-representable
    numbers for that k has zero asymptotic density. (Forward direction.) -/
lemma main_conjecture_impl_density_zero (k : ℕ) (hMC : Filter.Eventually (RepresentableWith · k) Filter.atTop) :
    ¬ ∃ (δ : ℝ), δ > 0 ∧ Filter.Eventually (λ (N : ℕ) => ((by
        classical
        exact ((Finset.filter (λ n => ¬ RepresentableWith n k) (Finset.range N)).card : ℝ)) / (N : ℝ) ≥ δ)) Filter.atTop := by
  sorry

/-- A covering system for k=1: if every integer n falls into some congruence
    class (a,m) such that for all primes p and all e≥0 we have
    p + 2^e not congruent to a (mod m), then MainConjecture fails for k=1.

    Note: The condition must also cover the S=∅ case (where n = p, i.e. 2^0 = 1,
    so p + 2^0 = p + 1). So the condition for e=0 already handles the S=∅ case
    because when S=∅, we have Sum(S) = 0, and the representation is p = n,
    but the covering system blocks p + 1, not p. So we need the condition
    to block p as well. We include both blocking conditions for clarity. -/
lemma covering_system_blocks_k1 : (∃ (A : Finset (ℕ × ℕ)),
    (∀ n : ℕ, ∃ (a : ℕ) (m : ℕ), (a, m) ∈ A ∧ n ≡ a [MOD m]) ∧
    (∀ a m, ((a, m) ∈ A) → (∀ (p' : ℕ), Nat.Prime p' → ¬ (p' ≡ a [MOD m])) ∧
      ∀ (e : ℕ) (p' : ℕ), Nat.Prime p' → ¬ (p' + 2^e ≡ a [MOD m]))) →
    ¬ Filter.Eventually (RepresentableWith · 1) Filter.atTop := by
  intro h
  rcases h with ⟨A, hA_cover, hA_block⟩
  intro h
  rcases Filter.eventually_atTop.mp h with ⟨M, hM⟩
  rcases hA_cover (M+1) with ⟨a, m, hA_mem, hcong⟩
  rcases hA_block a m hA_mem with ⟨hA_block_p, hA_block_pe⟩
  have h_rep : RepresentableWith (M+1) 1 := hM (M+1) (by omega)
  rcases h_rep with ⟨p, S, hp, hp_le, hS_card, h_sum_eq⟩
  by_cases hS_empty : S = ∅
  · subst hS_empty
    simp at h_sum_eq
    have h_eq : p = M+1 := by omega
    subst h_eq
    exact hA_block_p (M+1) hp hcong
  · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    have hS_card1' : S.card = 1 := by
      have : 1 ≤ S.card := Finset.one_le_card.mpr hS_nonempty
      omega
    rcases Finset.card_eq_one.mp hS_card1' with ⟨e, hS⟩
    subst hS
    simp at h_sum_eq
    have h_eq : p + 2^e = M+1 := by omega
    have h_mod : p + 2^e ≡ a [MOD m] := by
      calc
        p + 2^e = M+1 := h_eq
        _ ≡ a [MOD m] := hcong
    exact hA_block_pe e p hp h_mod

-- EVOLVE-BLOCK-END

end Erdos10
