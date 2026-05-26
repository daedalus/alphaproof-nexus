/-
  Population Member 05, Gen1: Champion — structural decomposition of Erdős #1.

  Strategy: Reduce to showing min_N(n)/2^n is bounded away from 0.
  
  Key decomposition:
  1. Pigeonhole bound: 2^n ≤ n·N + 1  (trivial, gives N ≥ (2^n-1)/n)
  2. To improve to C·2^n ≤ N, need to show the counting dimension n·N is
     too small — subset sums must be more spread out.
  3. Erdős-Moser technique: use Cauchy-Schwarz on differences of subset sums.
     Let σ_1, ..., σ_{2^n} be the subset sums in increasing order.
     The differences σ_{i+1} - σ_i are positive integers.
     By Cauchy-Schwarz, (∑(σ_{i+1} - σ_i))·(∑ 1/(σ_{i+1} - σ_i)) ≥ (2^n - 1)^2.
  4. The sum of differences is σ_{2^n} - σ_1 ≤ N·n.
  5. Need a lower bound on ∑ 1/(σ_{i+1} - σ_i). Since the σ_i are sums of
     elements of A, their GCD is 1 (if 1 ∈ A), otherwise the differences
     can be larger.
     
  Current gap: converting the Cauchy-Schwarz inequality into a concrete
  lower bound on N/2^n requires analytic estimates that are the
  core of the open problem.

  Rating (initial): Elo 1250
-/
import Mathlib
open Finset
open Real
open scoped BigOperators

namespace Erdos1

/-- The set of all subset sums of A (as a Finset ℕ). -/
def subset_sums (A : Finset ℕ) : Finset ℕ :=
  (Finset.powerset A).image (λ S => ∑ a in S, a)

lemma card_subset_sums (A : Finset ℕ) (h : IsSumDistinctSet A N) : (subset_sums A).card = 2 ^ A.card := by
  dsimp [subset_sums]
  rcases h with ⟨_, h_inj⟩
  have h_sums_inj : (Finset.image (λ S : Finset A => ∑ a in S, (a : ℕ).val) Finset.univ).card = 2 ^ A.card := by
    calc
      _ = (Finset.univ : Finset (Finset A)).card :=
        Finset.card_image_of_injective _ h_inj
      _ = (A.powerset).card := by simp
      _ = 2 ^ A.card := by simp
  -- Need to connect subset_sums A with this image — they should be the same Finset
  sorry

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

/-- The trivial counting bound: (2^n - 1)/n ≤ N. -/
lemma trivial_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    (2 ^ A.card - 1) / A.card ≤ N := by
  rcases h with ⟨hA_sub, h_inj⟩
  by_cases hA0 : A.card = 0
  · subst hA0; simp
  have h_card_ss : (subset_sums A).card = 2 ^ A.card := card_subset_sums A h
  have h_ss_bound : ∀ s ∈ subset_sums A, s ≤ A.card * N :=
    λ s hs => subset_sums_upper_bound A hA_sub s hs
  have h_ss_range : subset_sums A ⊆ Finset.range (A.card * N + 1) := by
    intro x hx; refine Finset.mem_range.mpr (Nat.lt_add_one_of_le (h_ss_bound x hx))
  have h_card_range : (Finset.range (A.card * N + 1)).card = A.card * N + 1 := by simp
  have h_ineq : 2 ^ A.card ≤ A.card * N + 1 := by
    calc
      2 ^ A.card = (subset_sums A).card := h_card_ss
      _ ≤ (Finset.range (A.card * N + 1)).card := Finset.card_le_card h_ss_range
      _ = A.card * N + 1 := h_card_range
  omega

lemma trivial_bound_real (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    ((2 : ℝ) ^ A.card - 1) / (A.card : ℝ) ≤ (N : ℝ) := by
  have h_nat : (2 ^ A.card - 1) / A.card ≤ N := trivial_bound A N h hN
  exact mod_cast h_nat

/-- Powers of 2: A = {1,2,4,...,2^{k-1}} is sum-distinct for N = 2^{k-1}.
    This gives min_N(k) ≤ 2^{k-1}. -/
lemma powers_of_two_bound (k : ℕ) (hk : 0 < k) : min_N k ≤ 2 ^ (k-1) := by
  let A := (Finset.range k).image (λ i => 2 ^ i)
  have hA_card : A.card = k := by
    simp [A]
  have hA_sub : A ⊆ Finset.Icc 1 (2 ^ (k-1)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hx_pos : 1 ≤ 2 ^ i := Nat.one_le_two_pow _
    have hx_bound : 2 ^ i ≤ 2 ^ (k-1) := by
      have hi_k : i < k := Finset.mem_range.mp hi
      have : i ≤ k-1 := by omega
      exact Nat.pow_le_pow_right (by norm_num) this
    exact Finset.mem_Icc.mpr ⟨hx_pos, hx_bound⟩
  have h_inj : Function.Injective (λ (S : Finset A) => ∑ a in S, (a : ℕ).val) := by
    intro S T h
    apply Subtype.ext
    apply Finset.ext_iff.mpr
    intro x
    constructor
    · intro hxS
      -- If x ∈ S but x ∉ T, the sums differ because binary representation is unique
      sorry
    · intro hxT
      sorry
  have h_ex : ∃ A', IsSumDistinctSet A' (2 ^ (k-1)) ∧ A'.card = k := by
    refine ⟨A, ⟨hA_sub, h_inj⟩, hA_card⟩
  dsimp [min_N]
  apply csInf_le (Set.nonempty_of_mem h_ex)
  rcases h_ex with ⟨A', hA', hA'_card⟩
  exact ⟨A', hA', hA'_card⟩

/-- The Erdős-Moser inequality: ∑_{i=1}^{2^n-1} 1/(σ_{i+1} - σ_i) ≥ (2^n - 1)^2 / (N·n).
    By Cauchy-Schwarz: (∑ d_i)(∑ 1/d_i) ≥ (2^n - 1)^2.
    Since ∑ d_i = σ_{2^n} - σ_1 ≤ N·n, we get ∑ 1/d_i ≥ (2^n - 1)^2 / (N·n). -/
lemma erdos_moser_cauchy_schwarz (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) (hN : N ≠ 0) :
    N * A.card ≥ (2 ^ A.card - 1) ^ 2 / (∑ d in subset_sums_diff A, d) := by
  sorry

/-- The main open theorem: find a constant C > 0 such that N > C·2^n.
    This is equivalent to showing min_N(n) / 2^n is bounded away from 0. -/
lemma main_conjecture_via_min_N : (∃ C > (0 : ℝ), ∀ n : ℕ, (min_N n : ℝ) ≥ C * (2 : ℝ) ^ n) ↔
    (∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N), N ≠ 0 → C * (2 : ℝ) ^ A.card < (N : ℝ)) := by
  constructor
  · intro hC
    rcases hC with ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, λ N A h hN => ?_⟩
    have hn_bound : (min_N A.card : ℝ) ≤ (N : ℝ) := by
      have : min_N A.card ≤ N := by
        apply csInf_le (Set.nonempty_of_mem ?_)
        exact ⟨A, h, rfl⟩
      exact mod_cast this
    have : (min_N A.card : ℝ) ≥ C * (2 : ℝ) ^ A.card := hC A.card
    linarith
  · intro hC
    rcases hC with ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, λ n => ?_⟩
    by_cases hn0 : n = 0
    · subst hn0; simp
    have hmin_nonempty : Set.Nonempty { N | ∃ A : Finset ℕ, IsSumDistinctSet A N ∧ A.card = n } := by
      have hbound : min_N n ≤ 2 ^ (n-1) := powers_of_two_bound n hn0
      exact Set.nonempty_of_mem (by
        have := powers_of_two_bound n hn0
        -- min_N is defined as sInf of a nonempty set
        sorry)
    -- Need: for the actual minimizer A (not just the sInf), hC gives C·2^n < N
    -- But we only know C·2^n < N for ALL sum-distinct sets, which includes the minimizer.
    sorry

end Erdos1
