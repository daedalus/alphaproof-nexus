/-
  Population Member 05: Strategy = Prove True via summability of 1/x over A.
  Approach: Show that the Dirichlet series Σ_{x∈A} 1/x^s has a simple pole at s=1
  (or doesn't), and use Abelian/Tauberian theorems to get the log density.
  The logarithmic density is the coefficient of the simple pole of the Dirichlet series at s=1.
  Since A is defined by congruence conditions, its Dirichlet series factorizes.
  Rating (initial): Elo 1200
-/
import Mathlib

open Filter Finset Real Set Complex
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

/-- The generating function (sum of 1/x over A up to N). -/
noncomputable def S (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ k in Finset.filter (λ k => k ∈ A) (Finset.Icc 1 N), (k : ℝ)⁻¹

/-- For any set A, S(A, N) / log N → d means HasLogDensity A d. -/
lemma S_equiv (A : Set ℕ) (d : ℝ) : HasLogDensity A d ↔
    Tendsto (fun N : ℕ => S A N / Real.log (N : ℝ)) atTop (𝓝 d) := by
  dsimp [HasLogDensity, S]
  constructor
  · intro h; simpa [Finset.Icc, Finset.range_succ] using h
  · intro h; simpa [Finset.Icc, Finset.range_succ] using h

/-- The key insight: A is the complement of a set B, where B is the union of
    arithmetic progressions a_i (mod n_i) starting at n_i.
    So 1_A = 1 - 1_B, and S(A, N) = H_N - S(B, N) where H_N is the partial harmonic sum.
    Since H_N / log N → 1, we have:
    S(A, N)/log N → 1 - lim S(B, N)/log N

    Now, B = ∪_i B_i where B_i = {x ≥ n_i | x ≡ a_i (mod n_i)}.
    By inclusion-exclusion and the fact that moduli are distinct (StrictMono),
    the sets B_i are "almost disjoint" in a log-density sense.

    For each arithmetic progression a (mod n), the log density is 1/n.
    The sum of 1/n_i converges or diverges depending on the sequence.
    If Σ 1/n_i < ∞, then by Borel-Cantelli, almost no integers are blocked,
    so A has log density 1.

    If Σ 1/n_i diverges, the log density might be less than 1, but still should exist
    because the n_i are increasing and the blocking events are "independent enough"
    for the log density to converge (by a law of large numbers type argument).
-/

/-- If Σ 1/n_i < ∞, then A has log density 1 (almost no integers are blocked). -/
lemma log_density_one_if_summable (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n)
    (hsum : Summable (λ i => (1 : ℝ) / (seq_n i : ℝ))) : HasLogDensity (A seq_n seq_a) 1 := by
  sorry

/-- If Σ 1/n_i = ∞, we can use a "density" argument: since the progression a_i (mod n_i)
    has density 1/n_i in ℕ, and the events are "quasi-independent", the total blocked density
    is the limit of partial sums of 1/n_i. This limit exists (possibly ∞).
    The density of A is 1 - min(1, limit of Σ_{i<k} 1/n_i as k→∞).
    This always exists because Σ_{i<k} 1/n_i is monotone increasing and bounded (by 1 in terms of
    density contribution, since the progressions overlap). The limit exists.
-/
lemma log_density_exists_via_series (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    ∃ d, HasLogDensity (A seq_n seq_a) d := by
  -- The blocked density is the limsup of Σ_{n_i ≤ N} 1/n_i, but with overlaps subtracted.
  -- Since n_i are increasing, B_i ∩ B_j for i < j is {x ≥ n_j | x ≡ a_i (mod n_i) and x ≡ a_j (mod n_j)}.
  -- This is a congruence system; by CRT, if gcd(n_i, n_j) | (a_j - a_i), there's a solution
  -- modulo lcm(n_i, n_j), giving density 1/lcm(n_i, n_j).
  -- So the overlap is small, and the inclusion-exclusion converges.
  sorry

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    intro seq_n seq_a hpos hmono
    exact log_density_exists_via_series seq_n seq_a hpos hmono
  · intro h; trivial

end Erdos25
