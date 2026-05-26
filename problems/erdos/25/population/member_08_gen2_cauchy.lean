/-
  Population Member 08, Gen2: Direct liminf/limsup approach.
  
  Strategy: Show that for any ε > 0, the liminf and limsup of S(N)/log N differ by at most ε.
  Use the fact that A is defined by "delayed" congruence conditions. Between N and 2N,
  the additional blocked elements are at most Σ_{n_i ≤ 2N} (1/n_i)·(2N - N + O(1)).
  Since n_i is strictly increasing, the number of i with n_i ≤ 2N is at most 2N.
  
  Key inequality: |S(2N)/log(2N) - S(N)/log N| ≤ C / log N for some constant C,
  provided the sequence n_i grows fast enough. For general sequences, we need a
  more delicate bound.
  
  Rating (initial): Elo 1250
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

/-- Decay of increments: for any sequences, the difference |S(2N) - S(N)|/log(2N) → 0.
    This follows from the fact that at most half the elements are newly added between N and 2N,
    and they contribute at most log(2) to the harmonic sum. -/
lemma increment_decay (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    Tendsto (fun N : ℕ => 
      |((∑ x in Finset.filter (λ x => x ∈ A seq_n seq_a) (Finset.Icc (N+1) (2*N)), (x : ℝ)⁻¹) : ℝ) / Real.log (2*(N:ℝ))|)
      atTop (𝓝 0) := by
  sorry

/-- The sequence S(N)/log N is a Cauchy sequence.
    Proof: For any M > N, write M as iterative doubling: N, 2N, 4N, ..., ≤ M.
    Each doubling step contributes a small amount (tends to 0 as N → ∞).
    The total number of steps is O(log(M/N)), but each step is o(1) as N → ∞.
    So for large enough N, the total variation beyond N is < ε. -/
lemma S_cauchy (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    CauchySeq (fun N : ℕ => 
      (∑ x in Finset.filter (λ x => x ∈ A seq_n seq_a) (Finset.Icc 1 N), (x : ℝ)⁻¹) / Real.log (N : ℝ)) := by
  sorry

/-- Since ℝ is complete, the Cauchy sequence converges → log density exists. -/
lemma universal_via_cauchy : UniversalStatement := by
  intro seq_n seq_a hpos hmono
  have h_cauchy := S_cauchy seq_n seq_a hpos hmono
  have h_complete : CompleteSpace ℝ := by infer_instance
  have h_conv : ∃ d, Tendsto (fun N : ℕ => 
      (∑ x in Finset.filter (λ x => x ∈ A seq_n seq_a) (Finset.Icc 1 N), (x : ℝ)⁻¹) / Real.log (N : ℝ)) atTop (𝓝 d) :=
    ⟨limUnder _, tendsto_nhds_of_cauchySeq h_cauchy⟩
  rcases h_conv with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  dsimp [HasLogDensity]
  -- Need to convert from Icc 1 N to range (N+1). The difference is just the term x=0 which is 0.
  simpa [Finset.range_succ, Finset.Icc, Finset.filter_insert, Finset.Ico] using hd

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    exact universal_via_cauchy
  · intro h; trivial

end Erdos25
