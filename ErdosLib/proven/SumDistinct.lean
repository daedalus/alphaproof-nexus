import Mathlib
open Finset

namespace ErdosLib

/-- A subset A of {1..N} with all subset sums distinct. -/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ (Function.Injective (λ (S : Finset A) => ∑ a in S, (a : ℕ).val))

/-- The set of all subset sums of A (as a Finset ℕ). -/
def subset_sums (A : Finset ℕ) : Finset ℕ :=
  (Finset.powerset A).image (λ S => ∑ a in S, a)

lemma subset_sums_upper_bound (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    ∀ s ∈ subset_sums A, s ≤ A.card * N := by
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨S, hS, rfl⟩
  have hS_sub_A : S ⊆ A := Finset.mem_powerset.mp hS
  calc
    (∑ a in S, a) ≤ (∑ a in S, N) :=
      Finset.sum_le_sum (λ a ha => (Finset.mem_Icc.mp (hA (hS_sub_A ha))).2)
    _ = S.card * N := by simp
    _ ≤ A.card * N := Nat.mul_le_mul_right N (Finset.card_le_card hS_sub_A)

/-- The trivial counting bound: 2^n distinct subset sums in [0, n·N].
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

lemma trivial_bound_real (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    ((2 : ℝ) ^ A.card - 1) / (A.card : ℝ) ≤ (N : ℝ) := by
  have h_nat : (2 ^ A.card - 1) / A.card ≤ N := trivial_bound A N h hN
  exact mod_cast h_nat

/-- The powers of 2 set: {2^0, 2^1, ..., 2^{k-1}}. -/
def powers_of_two_set (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (λ i => 2 ^ i)

lemma sum_range_pow_two_eq (j : ℕ) : (∑ i in Finset.range j, (2 : ℕ) ^ i) = (2 : ℕ) ^ j - 1 := by
  induction' j with j ih
  · simp
  · rw [Finset.sum_range_succ, ih, pow_succ]; omega

lemma sum_range_pow_two_lt (j : ℕ) : (∑ i in Finset.range j, (2 : ℕ) ^ i) < (2 : ℕ) ^ j := by
  have := sum_range_pow_two_eq j; omega

lemma card_powers_of_two_set (k : ℕ) : (powers_of_two_set k).card = k := by
  simp [powers_of_two_set]

lemma powers_of_two_set_subset_Icc (k : ℕ) : powers_of_two_set k ⊆ Finset.Icc 1 (2 ^ (k-1)) := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
  have hx_pos : 1 ≤ 2 ^ i := Nat.one_le_two_pow _
  have hx_bound : 2 ^ i ≤ 2 ^ (k-1) := by
    have hi_k : i < k := Finset.mem_range.mp hi
    have : i ≤ k-1 := by omega
    exact Nat.pow_le_pow_right (by norm_num) this
  exact Finset.mem_Icc.mpr ⟨hx_pos, hx_bound⟩

/-- min_N(n) = smallest N allowing a sum-distinct set of size n. -/
noncomputable def min_N (n : ℕ) : ℕ :=
  sInf { N | ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = n }

end ErdosLib
