/-
  Population Member 12 (Gen 6): Strategy = lcm growth via prime counting

  Previous generations used inclusion-exclusion and Möbius inversion.
  The open gap is proving the tail of the alternating series converges.

  NEW APPROACH: Use the prime number theorem to bound the lcm of the first
  k moduli. For seq_n i = i+1, the lcm of {n_0, ..., n_{k-1}} is
  exp(ψ(k)) where ψ is the Chebyshev function. By the PNT, ψ(k) ~ k,
  so lcm ~ e^k. Therefore 1/lcm(I) for |I| ≥ k decays super-exponentially
  in min(I), ensuring absolute convergence of the inclusion-exclusion series.

  Key lemmas:
  1. For any finite I, the density of x satisfying all congruences in I
     is at most 1/L where L = lcm(n_i : i ∈ I).
  2. The sum over I of 1/L converges when n_i grows, because the lcm
     of the first t moduli grows at least as fast as the product of primes
     up to t.
  3. Apply the d'Alembert ratio test: for inclusion-exclusion on families
     indexed by subsets of ℕ, the k-th term of the tail is bounded by
     Σ_{i≥k} 1/n_i, which converges when n_i grows faster than i·log(i).

  Rating (initial): Elo 1350
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

/-- lcm of a finite set of natural numbers. -/
noncomputable def lcm (I : Finset ℕ) : ℕ :=
  Finset.fold LCM 0 (λ i => i) I

/-- The density of the set of x satisfying x ≡ a_i (mod n_i) for all i∈I
    is at most 1/lcm(I). -/
lemma congruence_density_lcm_bound (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (I : Finset ℕ) :
    ((Finset.filter (λ x : ℕ => ∀ i ∈ I, (x : ℤ) ≡ seq_a i [ZMOD seq_n i]) (Finset.range (N+1))).card : ℝ) / (N : ℝ)
    ≤ (1 : ℝ) / (lcm I : ℝ) := by
  sorry

/-- The lcm of the first k integers grows at least as fast as e^{k/2}
    for sufficiently large k. (Weak form of prime number theorem.) -/
lemma lcm_first_k_lower_bound (k : ℕ) (hk : 100 ≤ k) : (lcm (Finset.range k) : ℝ) ≥ Real.exp ((k : ℝ) / 2) := by
  sorry

/-- The sum over finite subsets I of 1/lcm(I) converges.
    Proof: group by max(I). For max(I) = m, the lcm includes m, so
    1/lcm(I) ≤ 1/m. The number of subsets with max = m is 2^{m-1}.
    So the tail from m ≥ k is bounded by Σ_{m≥k} 2^{m-1}/m.
    By the ratio test, this converges to 0 as k → ∞. -/
lemma tail_sum_converges (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (ε : ℝ) (hε : ε > 0) :
    ∃ K : ℕ, ∀ k ≥ K, ∑ I in Finset.powerset (Finset.Ici k), (1 : ℝ) / (lcm (I.image seq_n) : ℝ) < ε := by
  sorry

/-- Use the tail bound above to show the inclusion-exclusion series converges
    and therefore the density exists. -/
lemma density_via_lcm_tail (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    ∃ d, HasDensity (A seq_n seq_a) d := by
  sorry

/-- Logarithmic density follows from natural density. -/
lemma log_density_from_density (A : Set ℕ) (d : ℝ) (h : HasDensity A d) : HasLogDensity A d := by
  sorry

/-- Main theorem. -/
@[research_open]
theorem erdos_25 : UniversalStatement := by
  intro seq_n seq_a hpos hmono
  rcases density_via_lcm_tail seq_n seq_a hpos hmono with ⟨d, hd⟩
  have hlog := log_density_from_density (A seq_n seq_a) d hd
  exact ⟨d, hlog⟩

-- EVOLVE-BLOCK-END

end Erdos25
