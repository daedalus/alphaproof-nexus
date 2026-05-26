/-
  Population Member 03: Strategy = Prove False via counterexample construction.
  Approach: Construct sequences n_i, a_i such that A has no logarithmic density.
  Use a "thinning" construction: make A oscillate between thin and thick intervals,
  preventing the limit from converging.
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

/--
Construct a counterexample.
Strategy: Let n_i = 2^i (or any fast-growing sequence).
Choose a_i cleverly so that A is alternately very dense and very sparse.
The classic Besicovitch construction for natural density uses X_n = {0}.
For logarithmic density, we need a stronger oscillation.

Conjecture: set a_i = 0 for all i. Then A = {x | ∀ i: 2^i > x or 2^i ∤ x}.
This is the complement of all powers of 2 dividing x.
This set might have no logarithmic density because...
-/
def counterexample_n (i : ℕ) : ℕ := 2 ^ (i+1)
def counterexample_a (i : ℕ) : ℤ := 0

lemma counterexample_pos : ∀ i, 0 < counterexample_n i := by
  intro i; simp [counterexample_n]

lemma counterexample_strictMono : StrictMono counterexample_n := by
  intro i j h; simp [counterexample_n]; exact Nat.pow_lt_pow_right (by omega) h

/-- The set A for this counterexample: x ∈ A iff for all i with 2^(i+1) ≤ x, 2^(i+1) ∤ x.
    Equivalently: x is NOT divisible by any power of 2 greater than 1 up to x.
    This means x is a power of 2 itself! Because every x has a unique 2-adic valuation.
    Wait... If 2 ∤ x, then x is odd → all 2^(i+1) ∤ x for every i.
    So A contains all odd numbers. And x = 2^k: then for i+1 = k, 2^(i+1) = 2^k which divides x.
    But 2^(i+1) ≤ x means i+1 ≤ k, and for i+1 = k, 2^(i+1) = 2^k | 2^k, so 2^k ∉ A.
    So A = set of odd numbers. That has density 1/2, both natural and logarithmic.
    This is NOT a counterexample!

Need a more clever construction. Perhaps use alternating residues to create oscillation.
-/
lemma A_is_all_odds_for_pow2 : A counterexample_n counterexample_a = { x : ℕ | ¬ Even x } := by
  ext x; dsimp [A, counterexample_n, counterexample_a]; constructor
  · intro h; by_contra! hx; have hx' : Even x := hx
    rcases hx' with ⟨k, hk⟩
    have hk' : 2^1 = 2 := by norm_num
    sorry
  · sorry

/--
Alternative: Let n_i = i+1 (all moduli). Then the condition is:
x ∈ A iff for all i with i+1 ≤ x, x ≢ a_i (mod i+1).
Since we cover ALL moduli, this is like saying x avoids a specific residue for every modulus ≤ x.
This is a covering system! For clever choice of a_i, A could be empty or have no density.
-/
def counterexample_n_v2 (i : ℕ) : ℕ := i+1

/-- Use the mod 2 residue to alternatively block and unblock large intervals. -/
def counterexample_a_v2 (i : ℕ) : ℤ :=
  if h : i = 0 then 0 else
  if i = 1 then 1 else
  0

/-- The set A for v2: x is odd iff it avoids the residue 1 mod 2.
    For i=0: modulus 1, residue 0. Since n_0 = 1 ≤ x for all x, the condition is:
    x ≢ 0 (mod 1), which is impossible. So A is empty!
    This is a trivial counterexample... A = ∅ has log density 0.

    Need something more subtle. Let's use n_i = p_i (primes) and a_i = 0.
    Then A = {x | ∀ p_i ≤ x, p_i ∤ x} = {1}. This has log density 0.
    Still not a counterexample.

The real challenge: is there ANY sequence for which A has no log density?
If Erdős and others haven't found one, maybe the answer is True after all.
-/
lemma A_is_singleton_for_primes : A (fun i => Nat.primes i) (λ _ => 0) = {1} := by
  ext x; constructor
  · intro hx; dsimp [A] at hx
    have : x = 1 := by
      by_contra! h
      have hp := Nat.exists_infinite_primes x
      sorry
    exact Set.mem_singleton_iff.mpr this
  · intro hx; rcases Set.mem_singleton_iff.mp hx with rfl
    intro i; left; have : 0 < Nat.primes i := Nat.prime_pos (Nat.nth_prime i).2
    omega

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    -- We try to construct a counterexample
    -- If we find one, we need to return ¬ UniversalStatement instead
    -- For now, we leave this open
    sorry
  · intro h; trivial

end Erdos25
