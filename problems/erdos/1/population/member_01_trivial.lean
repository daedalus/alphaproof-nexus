/-
  Population Member 01, Gen0: Trivial lower bound.
  
  Proves: (2^n - 1)/n ≤ N for any sum-distinct set A of size n in [1,N].
  
  Follows from: |powerset(A)| = 2^n, subset sums are distinct, each ≤ n·N.
  
  Rating (initial): Elo 1200
-/
import Mathlib
open Finset

namespace Erdos1

/-- The trivial counting bound.
    Distinct subset sums → 2^n distinct integers in [0, A.card·N] → 2^n ≤ A.card·N + 1. -/
lemma trivial_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    (2 ^ A.card - 1) / A.card ≤ N := by
  rcases h with ⟨hA_sub, h_inj⟩
  by_cases hA0 : A.card = 0
  · subst hA0; simp
  have h_card_ps : (A.powerset : Finset (Finset ℕ)).card = 2 ^ A.card := by
    simp
  have h_sum_bound : ∀ S, S ∈ A.powerset → (∑ a in S, a) ≤ A.card * N := by
    intro S hS
    have hS_sub_A : S ⊆ A := Finset.mem_powerset.mp hS
    have hS_sub_Icc : S ⊆ Finset.Icc 1 N := Finset.Subset.trans hS_sub_A hA_sub
    calc
      (∑ a in S, a) ≤ (∑ a in S, N) :=
        Finset.sum_le_sum (λ a ha => (Finset.mem_Icc.mp (hS_sub_Icc ha)).2)
      _ = S.card * N := by simp
      _ ≤ A.card * N := Nat.mul_le_mul_right N (Finset.card_le_card hS_sub_A)
  let f : A.powerset → ℕ := λ ⟨S, hS⟩ => ∑ a in S, a
  have hf_inj : Function.Injective f := h_inj
  have hf_image_sub : Finset.image f Finset.univ ⊆ Finset.range (A.card * N + 1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨⟨S, hS⟩, _, rfl⟩
    refine Finset.mem_range.mpr (Nat.lt_add_one_of_le (h_sum_bound S hS))
  have h_card_image : (Finset.image f Finset.univ).card = (A.powerset).card :=
    Finset.card_image_of_injective _ hf_inj
  have h_card_range : (Finset.range (A.card * N + 1)).card = A.card * N + 1 := by simp
  have h_ineq : 2 ^ A.card ≤ A.card * N + 1 := by
    calc
      2 ^ A.card = (A.powerset).card := by simp
      _ = (Finset.image f Finset.univ).card := by symm; exact h_card_image
      _ ≤ (Finset.range (A.card * N + 1)).card := Finset.card_le_card hf_image_sub
      _ = A.card * N + 1 := h_card_range
  omega

end Erdos1
