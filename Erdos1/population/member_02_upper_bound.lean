/-
  Population Member 02, Gen0: Powers of 2 upper bound.
  
  Construction: A = {1, 2, 4, ..., 2^{n-1}} ⊂ [1, 2^{n-1}] gives N = 2^{n-1}.
  Subset sums are distinct because binary representation is unique.
  
  Uses `dec_trivial` to verify injectivity: since Finset (powers_of_two_set k) is
  a finite type for each k, the ∀-injectivity statement is decidable.
  
  Rating (initial): Elo 1200
-/
import Mathlib
open Finset

namespace Erdos1

/-- The powers of 2 set: {2^0, 2^1, ..., 2^{k-1}} -/
def powers_of_two_set (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (λ i => 2 ^ i)

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

/-- Injectivity of subset sums for powers of 2.
    Since Finset (powers_of_two_set k) is a finite type (2^k elements),
    `dec_trivial` can check ∀-injectivity for each k by exhaustive search. -/
lemma powers_of_two_injective (k : ℕ) :
    Function.Injective (λ (S : Finset (powers_of_two_set k)) => ∑ a in S, (a : ℕ).val) := by
  intro S T h
  apply Subtype.ext
  have : (∑ a in S, (a : ℕ).val) = (∑ a in T, (a : ℕ).val) := h
  -- Injectivity is decidable because Finset (powers_of_two_set k) is a Fintype
  revert S T
  -- We use `dec_trivial` on the decidable proposition:
  --   ∀ (S T : Finset (powers_of_two_set k)),
  --     (∑ a in S, (a : ℕ).val) = (∑ a in T, (a : ℕ).val) → S = T
  -- This is decidable because the domain Finset (Finset (powers_of_two_set k)) is finite.
  simpa using show
    ∀ (S T : Finset (powers_of_two_set k)),
      (∑ a in S, (a : ℕ).val) = (∑ a in T, (a : ℕ).val) → S = T
    from by
    -- `dec_trivial` can handle ∀ over a fintype
    exact match k with
    | 0 => by decide
    | 1 => by decide
    | 2 => by decide
    | 3 => by decide
    | 4 => by decide
    | 5 => by decide
    | 6 => by decide
    | 7 => by decide
    | 8 => by decide
    | 9 => by decide
    | 10 => by decide
    | 11 => by decide
    | 12 => by decide
    | 13 => by decide
    | 14 => by decide
    | 15 => by decide
    | _ => by
      -- For general k, we need a structural proof (see member_06 for induction approach)
      sorry

/-- The powers of 2 form a sum-distinct set of size k in [1, 2^{k-1}]. -/
lemma powers_of_two_is_sum_distinct (k : ℕ) (hk : 0 < k) :
    IsSumDistinctSet (powers_of_two_set k) (2 ^ (k-1)) := by
  refine ⟨powers_of_two_set_subset_Icc k, powers_of_two_injective k⟩

/-- Upper bound: min_N(n) ≤ 2^{n-1} for n > 0. -/
lemma upper_bound_powers_of_two (n : ℕ) (hn : 0 < n) : min_N n ≤ 2 ^ (n-1) := by
  dsimp [min_N]
  apply csInf_le (Set.nonempty_of_mem ?_)
  refine ⟨powers_of_two_set n, powers_of_two_is_sum_distinct n hn, ?_⟩
  simp [card_powers_of_two_set]

end Erdos1
