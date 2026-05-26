/-
  Population Member 06, Gen1: Strategy = Prove True via measure-theoretic framework.
  
  Key insight: The condition for A can be rephrased as: for each modulus n_i, we remove
  the arithmetic progression a_i + n_i·ℤ, but only starting at n_i. Since n_i → ∞,
  each progression only affects numbers beyond a threshold that grows.
  
  This is like a "cutoff" version of the classical "Erdos-Selfridge" or "Davenport-Erdős"
  setting. The key difference from the classical setting is the "delayed activation" of
  each congruence.
  
  Approach: Model the indicator function 1_A as a product of (1 - f_i) where
  f_i(x) = 1 if n_i ≤ x and x ≡ a_i (mod n_i), else 0.
  Then show that the log-average of 1_A converges using the fact that the f_i
  are "almost uncorrelated" (the delays create a martingale-like structure).
  
  Rating (initial): Elo 1200
-/
import Mathlib

open Filter Finset Real Set MeasureTheory
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

/-- Indicator of whether modulus i blocks x: returns 1 if n_i ≤ x and x ≡ a_i (mod n_i), else 0. -/
def f (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (i : ℕ) (x : ℕ) : ℝ :=
  if h : seq_n i ≤ x ∧ ((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) then 1 else 0

lemma f_nonneg (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (i x : ℕ) : 0 ≤ f seq_n seq_a i x := by
  dsimp [f]; split <;> norm_num

lemma f_le_one (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (i x : ℕ) : f seq_n seq_a i x ≤ 1 := by
  dsimp [f]; split <;> norm_num

/-- x ∈ A iff f_i(x) = 0 for all i. -/
lemma A_iff_f_zero (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (x : ℕ) : x ∈ A seq_n seq_a ↔ ∀ i, f seq_n seq_a i x = 0 := by
  dsimp [A, f]
  constructor
  · intro h i; rcases h i with (hlt | hne)
    · by_cases hseq : seq_n i ≤ x
      · exfalso; exact Nat.not_lt.mpr hseq hlt
      · simp [hseq]
    · simp [hne]
  · intro h i
    have hi := h i
    dsimp at hi
    split at hi
    · exact Or.inr hi.2
    · exact Or.inl (by omega)

/-- The log density of A can be expressed as the limit of average blocking probability.
    If the events "i blocks x" are "rare enough" or "independent enough", the limit exists. -/
lemma log_density_via_indicators (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i)
    (hmono : StrictMono seq_n) : ∃ d, HasLogDensity (A seq_n seq_a) d := by
  -- For each N, the proportion of x in [1,N] not blocked by any i is
  -- something like (1 - 1/n_i) for "independent" blocks. But here blocks are
  -- not independent and have thresholds.
  -- The logarithmic density d = lim_{N→∞} (1/log N) Σ_{x ≤ N, x∈A} 1/x
  -- If we define S = Σ_{i} 1/n_i (sum of reciprocals), then:
  --   - If S < ∞: d = 1 (Borel-Cantelli: almost no integers blocked)
  --   - If S = ∞: d = ∏_{i} (1 - 1/n_i) if independent, but not independent!
  -- The actual problem is much more subtle.
  sorry

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    intro seq_n seq_a hpos hmono
    exact log_density_via_indicators seq_n seq_a hpos hmono
  · intro h; trivial

end Erdos25
