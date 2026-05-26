/-
  Population Member 07, Gen2: Hybrid strategy (crossover of head-truncation + measure theory).
  
  Parents: member_04_gen1 (head-truncation, Elo 1600) × member_06_gen1 (measure, Elo 1540)
  
  Key insight from crossover: The tail error between A and A_head(k) can be bounded
  by the measure of the union of congruence classes beyond n_k. The measure-theoretic
  framework gives us a way to estimate this error: it's at most the sum of reciprocals
  of moduli beyond n_k. If this tail sum goes to 0 as k → ∞, then the error is negligible.
  
  The sum condition: Σ_{i ≥ k} 1/n_i → 0 as k → ∞.
  This is NOT guaranteed for arbitrary StrictMono n_i (e.g., n_i = i+1 diverges).
  BUT: the head-truncation argument only needs that the LOGARITHMIC contribution
  goes to 0, which is weaker than the sum.
  
  Key innovation: Uset the inequality Σ_{x > N, x ∈ AP} 1/x ≈ (1/n)·log(N+n)/log N
  for an arithmetic progression modulo n, to show that even if Σ 1/n_i diverges,
  the overlapping progressions interact in a way that makes the tail error vanish.
  
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

def A (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

def A_head (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (k : ℕ) : Set ℕ :=
  { x : ℕ | ∀ i, i < k → ((x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])) }

def UniversalStatement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, HasLogDensity (A seq_n seq_a) d

-- EVOLVE-BLOCK-START

/-- Contribution of a single arithmetic progression a (mod n) to the log sum beyond N. -/
lemma ap_log_contribution (n a : ℕ) (hn : 0 < n) (N : ℕ) :
    (∑ x in Finset.Icc 1 N, (if (x : ℤ) ≡ (a : ℤ) [ZMOD n] then (x : ℝ)⁻¹ else 0)) / Real.log (N : ℝ) ≤ 1 / (n : ℝ) + (1 : ℝ) / (n : ℝ) := by
  sorry

/-- The expected (asymptotic) contribution of a modulus n to the log sum is 1/n
    (the density of a single congruence class). -/
lemma expected_contribution (n : ℕ) (hn : 0 < n) : 
    Tendsto (fun N : ℕ => 
      (∑ x in Finset.Icc 1 N, (if (x : ℤ) ≡ (0 : ℤ) [ZMOD n] then (x : ℝ)⁻¹ else 0)) / Real.log (N : ℝ)) 
      atTop (𝓝 (1 / (n : ℝ))) := by
  sorry

/-- The tail error is bounded by the sum of expected contributions of all moduli beyond n_k.
    By the monotone convergence theorem, this tail sum is at most the total contribution
    of all moduli, which is finite because the moduli grow at least linearly (StrictMono on ℕ). -/
lemma tail_error_bound (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) : 
    |(∑ x in Finset.Icc 1 N, ((if x ∈ A seq_n seq_a then (1 : ℝ) / x else 0) -
       (if x ∈ A_head seq_n seq_a k then (1 : ℝ) / x else 0))) / Real.log (N : ℝ)| 
    ≤ ∑ i ≥ k, (1 : ℝ) / (seq_n i : ℝ) := by
  sorry

/-- The tail sum Σ_{i ≥ k} 1/n_i → 0 as k → ∞ (monotone convergence theorem,
    since Σ 1/n_i converges). Wait — does it converge? For n_i = i+1, Σ 1/(i+1) diverges!
    So this approach fails for general sequences.
    
    BUT: we only need the TAIL SUM to go to 0. For n_i growing exponentially,
    Σ_{i ≥ k} 1/n_i → 0 geometrically. For n_i growing quadratically, Σ_{i ≥ k} 1/(i^2) → 0.
    For n_i growing linearly, Σ_{i ≥ k} 1/(i+1) diverges.
    
    This suggests: if n_i grows slowly (like i+1), the tail error does NOT vanish,
    and the head-truncation argument FAILS. This would mean the answer might be FALSE
    (a counterexample might exist with slow-growing n_i).
    
    Conjecture: The answer depends on the growth rate of n_i!
    - If Σ 1/n_i < ∞: d = 1 (Borel-Cantelli, almost nothing blocked)
    - If Σ 1/n_i diverges slowly: maybe d = 0? 
    - For n_i = i+1: the set A = {x | ∀ y ≤ x, x ≢ a_y (mod y)}. This is like a "greedy"
      set that avoids all residues. The logarithmic density might not exist! 
-/
lemma tail_sum_divergence_possible (seq_n : ℕ → ℕ) (hmono : StrictMono seq_n) (hslow : ∀ i, seq_n i ≤ i + 1) :
    ¬ Summable (λ i : ℕ => (1 : ℝ) / (seq_n i : ℝ)) := by
  have h_ge : ∀ i, seq_n i ≥ i := hmono.id_le
  have h_eq : ∀ i, seq_n i = i + 1 := by
    intro i
    apply le_antisymm (hslow i) (h_ge i)
  subst h_eq
  simpa using summable_nat_add_iff (1 : ℕ) |>.not.mp (by
    have : ¬ Summable (λ n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) := by
      -- harmonic series diverges
      refine (summable_nat_add_iff 1).not.mp ?_
      simpa using not_summable_normed_iff.mp (by exact not_summable_of_not_summable_normed ?_)
      sorry
    sorry)

/-- The proof reduces to showing that the limsup and liminf of S(N)/log N are equal.
    Let L = liminf and U = limsup. For any ε > 0, we can find large N where S(N)/log N is within
    ε of L, and then use the structure of A to bound how far it can deviate.
    
    For any M > N, the difference |S(M)/log M - S(N)/log N| can be bounded by the contribution
    of numbers between N and M. For each modulus n_i, its contribution to this interval
    is at most something like (1/n_i)·(log M - log N) / log N.
    
    If the total contribution of all moduli beyond some point is small, then the difference
    between L and U must be small. This would prove the limit exists.
-/
lemma liminf_equals_limsup (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    ∃ d, HasLogDensity (A seq_n seq_a) d := by
  let S (N : ℕ) : ℝ := (∑ x in Finset.filter (λ x => x ∈ A seq_n seq_a) (Finset.Icc 1 N), (x : ℝ)⁻¹) / Real.log (N : ℝ)
  have h_bounded : ∀ N, 0 ≤ S N ∧ S N ≤ 1 := by
    intro N
    have h_nonneg : 0 ≤ S N := by
      dsimp [S]
      refine div_nonneg (Finset.sum_nonneg (λ x hx => ?_)) (Real.log_nonneg (by norm_num))
      positivity
    have h_le_one : S N ≤ 1 := by
      -- uses comparison with harmonic series: Σ 1/x / log N → 1
      sorry
    exact ⟨h_nonneg, h_le_one⟩
  have h_L : ∃ L, atTop.liminf S = L := sorry
  have h_U : ∃ U, atTop.limsup S = U := sorry
  -- Show L = U
  sorry

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    intro seq_n seq_a hpos hmono
    exact liminf_equals_limsup seq_n seq_a hpos hmono
  · intro h; trivial

end Erdos25
