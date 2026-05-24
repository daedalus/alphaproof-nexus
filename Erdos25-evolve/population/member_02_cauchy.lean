/-
  Population Member 02: Strategy = Prove True via Cauchy completeness.
  Approach: Show the partial sums (1/log N) Σ_{k∈A,k≤N} 1/k form a Cauchy sequence,
  hence converge (ℝ is complete). Bound the tail using the fact that
  each modulus n_i blocks at most 1/n_i fraction of integers.
  Rating (initial): Elo 1200
-/
import Mathlib

open Filter Finset Real Set
open scoped Topology
open Classical

set_option maxRecDepth 2000000

namespace Erdos25

noncomputable def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 d)

def A (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

def UniversalStatement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, HasLogDensity (A seq_n seq_a) d

-- EVOLVE-BLOCK-START

/-- Partial sum S(N) = (1/log N) * Σ_{k ≤ N, k ∈ A} 1/k -/
noncomputable def S (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (N : ℕ) : ℝ :=
  ((∑ k in Finset.filter (λ k => k ∈ A seq_n seq_a) (Finset.Icc 1 N), (k : ℝ)⁻¹) : ℝ) / Real.log (N : ℝ)

/-- Show S(N) is a Cauchy sequence by bounding |S(N) - S(M)| for M > N.
    Key idea: for k > N, whether k ∈ A only depends on moduli n_i ≤ k.
    Since n_i → ∞ (StrictMono), only finitely many moduli affect each tail. -/
lemma S_cauchy (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    CauchySeq (fun N : ℕ => S seq_n seq_a N) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  -- Need to find N₀ such that for all M, N ≥ N₀, |S(M) - S(N)| < ε
  -- Strategy: bound the contribution of x > N to the sum
  -- Since n_i ≥ i (StrictMono + positive), the i-th modulus kicks in at x = n_i
  -- For x > N, the "active moduli" are those with n_i ≤ x, which grows slowly
  sorry

/-- If S(N) is Cauchy, it converges (ℝ is complete). -/
lemma S_convergent (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    ∃ d, Tendsto (fun N : ℕ => S seq_n seq_a N) atTop (𝓝 d) := by
  have h_cauchy : CauchySeq (fun N : ℕ => S seq_n seq_a N) := S_cauchy seq_n seq_a hpos hmono
  -- ℝ is complete: Cauchy sequences converge
  rcases cauchy_iff.mp h_cauchy with ⟨h⟩
  -- Actually we need `Metric.complete_space ℝ` which is a theorem
  have h_complete : CompleteSpace ℝ := by infer_instance
  exact ⟨limUnder (fun N : ℕ => S seq_n seq_a N), tendsto_nhds_of_cauchySeq h_cauchy⟩

/-- S(N) → d implies HasLogDensity A d. -/
lemma S_tendsto_implies_hasLogDensity (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (d : ℝ) :
    Tendsto (fun N : ℕ => S seq_n seq_a N) atTop (𝓝 d) → HasLogDensity (A seq_n seq_a) d := by
  intro h
  -- S(N) and HasLogDensity differ: S uses Icc 1 N and divides by log N directly;
  -- HasLogDensity uses range (n+1) and divides by log n. Need to show these are equivalent.
  -- For large N, the difference between range (N+1) and Icc 1 N is negligible (adds 0).
  -- The log N denominator matches.
  dsimp [HasLogDensity, S] at h ⊢
  -- We need to relate the two sum formulations
  have h_sums : ∀ (N : ℕ), (∑ k in Finset.filter (λ k => k ∈ A seq_n seq_a) (Finset.range (N+1)), (k : ℝ)⁻¹) =
      (∑ k in Finset.filter (λ k => k ∈ A seq_n seq_a) (Finset.Icc 1 N), (k : ℝ)⁻¹) := by
    intro N
    apply Finset.sum_subset (Finset.filter_subset _ _) (by
      intro x hx hx'
      simp [Finset.mem_range, Finset.mem_Icc] at hx hx'
      -- x can be 0, but 1/0 is not defined... Actually (0:ℝ)⁻¹ = 0 in Lean? No, it's 0⁻¹.
      -- For x = 0, 1/x is defined as 0⁻¹ = 0 in ℝ? Let's check.
      -- Actually in ℝ, 0⁻¹ is defined as 0 by convention? No, it's defined as 0 by division ring.
      -- Wait, (0 : ℝ)⁻¹ is 0 in ℝ? No, Inv.inv 0 = 0 in ℝ by convention in DivisionRing.
      -- Actually `inv_zero` says (0 : ℝ)⁻¹ = 0. So 0 contributes 0.
      sorry)
    -- This isn't quite right... need to handle the difference.
    sorry
  sorry

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    intro seq_n seq_a hpos hmono
    rcases S_convergent seq_n seq_a hpos hmono with ⟨d, hd⟩
    exact ⟨d, S_tendsto_implies_hasLogDensity seq_n seq_a d hd⟩
  · intro h; trivial

end Erdos25
