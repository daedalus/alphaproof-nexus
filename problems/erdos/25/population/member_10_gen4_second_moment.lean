/-
  Population Member 10, Gen4: Strategy = "Second-moment / Euler product bound".

  Previous generations relied on tail-sum bound Σ_{i≥k} 1/n_i → 0, which fails
  for slow-growing n_i (e.g., n_i = i+2). This member tries a different angle:

  Use INCLUSION-EXCLUSION / SECOND-MOMENT to bound the error between A and
  A_head(k) beyond the union bound. For pairwise coprime moduli with residues 0,
  the density of A is exactly ∏_i (1 - 1/n_i), which always exists (may be 0).
  
  For general residues, use the Chinese Remainder Theorem to decompose the
  blocking events into independent contributions. The key estimate:
    |log-density(A_head(k)) - log-density(A)| ≤ Σ_{i≥k} 1/n_i²
  for the residue-0 case with coprime moduli (improved from Σ 1/n_i via
  inclusion-exclusion second-moment bound).

  Rating (initial): Elo 1300
-/
import Mathlib

open Filter Finset Real Set
open scoped Topology
open Classical

set_option maxRecDepth 2000000

namespace Erdos25

noncomputable def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 d)

noncomputable def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card : ℝ) / (n : ℝ)) atTop (𝓝 d)

def A (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

def UniversalStatement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, HasLogDensity (A seq_n seq_a) d

-- EVOLVE-BLOCK-START

/-- A_head(k): keep only first k constraints. Superset of A. -/
def A_head (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (k : ℕ) : Set ℕ :=
  { x : ℕ | ∀ i, i < k → ((x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])) }

lemma A_subset_A_head (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (k : ℕ) : A seq_n seq_a ⊆ A_head seq_n seq_a k := by
  intro x hx
  dsimp [A_head]
  intro i hi
  dsimp [A] at hx
  exact hx i

/-- For pairwise coprime moduli and residue 0, the density of A_head(k) is ∏_{i<k} (1 - 1/n_i). -/
lemma head_density_product_formula (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i) (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (seq_n i) (seq_n j)) (k : ℕ) :
    HasDensity (A_head seq_n (λ _ => 0) k) (∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ)))) := by
  sorry

/-- The product ∏_{i<k} (1 - 1/n_i) converges as k → ∞.
    The limit is > 0 if Σ 1/n_i converges, and = 0 if Σ 1/n_i diverges and n_i are bounded.
    In either case, the sequence converges to some L ∈ [0,1]. -/
lemma product_converges (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i) :
    ∃ L : ℝ, Tendsto (λ k : ℕ => ∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ)))) atTop (𝓝 L) := by
  have h_nonneg : ∀ i, 0 ≤ 1 - ((1 : ℝ) / (seq_n i : ℝ)) := by
    intro i
    have h_npos : (0 : ℝ) < seq_n i := by exact_mod_cast hpos i
    have : (1 : ℝ) / (seq_n i : ℝ) ≤ 1 := by
      refine (div_le_one ?_).mpr ?_
      · exact mod_cast hpos i
      · simp
    nlinarith
  have h_noninc : ∀ k, ∏ i in Finset.range (k+1), (1 - ((1 : ℝ) / (seq_n i : ℝ))) ≤
    ∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ))) := by
    intro k
    rw [Finset.prod_range_succ]
    refine mul_le_mul_of_nonneg_right ?_ (h_nonneg k)
    have : 1 - ((1 : ℝ) / (seq_n k : ℝ)) ≤ 1 := by nlinarith
    exact this
  have h_bounded : ∀ k, 0 ≤ ∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ))) := by
    intro k
    refine Finset.prod_nonneg h_nonneg
  -- Monotone nonincreasing sequence bounded below → converges
  let L := sInf (Set.range (λ k : ℕ => ∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ)))))
  have hL_le : ∀ k, L ≤ ∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ))) :=
    λ k => csInf_le (Set.range_nonempty _) ⟨k, rfl⟩
  have h_tendsto : Tendsto (λ k : ℕ => ∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ)))) atTop (𝓝 L) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h_exists : ∃ m, ∏ i in Finset.range m, (1 - ((1 : ℝ) / (seq_n i : ℝ))) < L + ε := by
      by_contra! h_all
      have h_bound : L + ε ≤ L := by
        apply le_csInf (Set.range_nonempty _)
        intro y hy
        rcases hy with ⟨m, rfl⟩
        exact h_all m
      nlinarith
    rcases h_exists with ⟨m, hm⟩
    refine Filter.eventually_atTop.mpr ⟨m, λ n hn => ?_⟩
    have h_noninc_nm : ∏ i in Finset.range n, (1 - ((1 : ℝ) / (seq_n i : ℝ))) ≤
      ∏ i in Finset.range m, (1 - ((1 : ℝ) / (seq_n i : ℝ))) := by
      -- iterate h_noninc from m to n
      revert n; refine Nat.le_induction (by rfl) (λ a ha h_prev => ?_) n hn
      calc
        ∏ i in Finset.range (a+1), (1 - ((1 : ℝ) / (seq_n i : ℝ))) ≤
          ∏ i in Finset.range a, (1 - ((1 : ℝ) / (seq_n i : ℝ))) := h_noninc a
        _ ≤ ∏ i in Finset.range m, (1 - ((1 : ℝ) / (seq_n i : ℝ))) := h_prev
    have h_diff : |∏ i in Finset.range n, (1 - ((1 : ℝ) / (seq_n i : ℝ))) - L| < ε := by
      have h_nonneg_diff : 0 ≤ ∏ i in Finset.range n, (1 - ((1 : ℝ) / (seq_n i : ℝ))) - L := by
        nlinarith [hL_le n, h_bounded n]
      have h_upper : ∏ i in Finset.range n, (1 - ((1 : ℝ) / (seq_n i : ℝ))) - L < ε := by
        nlinarith
      rw [abs_of_nonneg h_nonneg_diff]
      exact h_upper
    exact h_diff
  exact ⟨L, h_tendsto⟩

/-- For residue-0 coprime case, the second-moment bound improves the tail estimate:
    |density(A_head(k)) - density(A)| ≤ Σ_{i≥k} 1/n_i².
    
    This follows from inclusion-exclusion: the events "n_i divides x" are pairwise
    independent (by coprimality), so the second moment of the count of blocking
    factors is Σ 1/n_i², which converges even for divergent Σ 1/n_i. -/
lemma second_moment_bound (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i)
    (hcoprime : ∀ i j, i ≠ j → Nat.Coprime (seq_n i) (seq_n j)) (k : ℕ) :
    |∏ i in Finset.range k, (1 - ((1 : ℝ) / (seq_n i : ℝ))) - ∏ i : ℕ, (1 - ((1 : ℝ) / (seq_n i : ℝ)))| ≤
    ∑' i : ℕ, (1 : ℝ) / ((seq_n (i + k) : ℝ) ^ 2) := by
  sorry

/-- For arbitrary residues, use Chinese Remainder to reduce to residue-0 case via translation.
    If A has modulus n_i and residue a_i, then shifting by a_i gives a set with residue 0
    but different moduli. The density existence is invariant under translation. -/
lemma general_case_via_crt (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i)
    (hmono : StrictMono seq_n) : ∃ d, HasLogDensity (A seq_n seq_a) d := by
  -- Strategy: factor each modulus into prime powers; apply product formula per prime;
  -- combine via Chinese Remainder Theorem.
  -- For each prime p, consider the subsequence of moduli divisible by powers of p.
  -- Within each p-adic component, the residues can be normalized to 0 via translation.
  -- The product over p of (1 - p^{-a}) converges.
  sorry

/-- Main theorem: density exists for all sequences. -/
@[research_open]
theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    intro seq_n seq_a hpos hmono
    exact general_case_via_crt seq_n seq_a hpos hmono
  · intro h; trivial

-- EVOLVE-BLOCK-END
end Erdos25
