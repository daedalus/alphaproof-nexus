import Mathlib

open Filter Finset Real Set
open scoped Topology
open Classical

set_option maxRecDepth 2000000

/-!
# Erdős Problem 25: Logarithmic density of size-dependent congruences

*Reference:* [erdosproblems.com/25](https://www.erdosproblems.com/25)

Let $1 \leq n_1 < n_2 < \cdots$ be an arbitrary sequence of integers, each with an associated
residue class $a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for every $i$ either
$n < n_i$ or $n \not\equiv a_i \pmod{n_i}$. Must the logarithmic density of $A$ exist?

## Evolution sketch

This is generation 0 of the evolutionary search. The EVOLVE-BLOCK contains helper definitions
and decomposed lemmas. The core unknown is whether a counterexample can be constructed
(False) or if the density always exists (True).
-/

namespace Erdos25

/-- Logarithmic density of a set A ⊆ ℕ.
  Defined as lim_{n→∞} (1 / log n) * Σ_{k ≤ n, k ∈ A} 1/k. -/
noncomputable def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 d)

/-- The answer placeholder type (simulates the answer() elaborator). -/
inductive Answer : Type where
  | unknown
  | known (b : Bool)

/--
The set A as defined in the problem statement. An integer x is in A iff for every
modulus n_i, either x is below the threshold n_i or x avoids the forbidden residue.
-/
def A (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

lemma A_iff (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (x : ℕ) :
    x ∈ A seq_n seq_a ↔ ∀ i, seq_n i ≤ x → ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) := by
  dsimp [A]
  constructor
  · intro h i hi
    rcases h i with (hlt | hne)
    · exfalso; exact Nat.not_lt.mpr hi hlt
    · exact hne
  · intro h i
    by_cases hx : seq_n i ≤ x
    · right; exact h i hx
    · left; exact Nat.lt_of_not_ge hx

/-- The universal statement: for any sequences, the logarithmic density exists. -/
def UniversalStatement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, HasLogDensity (A seq_n seq_a) d

-- EVOLVE-BLOCK-START

/--
Davenport-Erdős theorem: when all residues are 0, the logarithmic density exists.
Reference: Davenport, H. and Erdős, P., "On sequences of integers" (1936).
-/
lemma davenport_erdos_case (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    ∃ d, HasLogDensity (A seq_n (λ _ => 0)) d := by
  sorry

/--
If a counterexample exists, there is a pair of sequences with no density.
This structure captures a concrete witnessing pair.
-/
structure Counterexample where
  seq_n : ℕ → ℕ
  seq_a : ℕ → ℤ
  hpos : ∀ i, 0 < seq_n i
  hmono : StrictMono seq_n
  h_no_density : ¬ ∃ d, HasLogDensity (A seq_n seq_a) d

/--
If a counterexample exists, the universal statement is false.
-/
lemma counterexample_implies_not_universal : Nonempty Counterexample → (¬ UniversalStatement) := by
  intro hce huni
  rcases hce with ⟨ce⟩
  apply ce.h_no_density
  exact huni ce.seq_n ce.seq_a ce.hpos ce.hmono

/--
Translation by a constant: A shifted by t.
-/
lemma translation_shift (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (t : ℤ) :
    A seq_n seq_a = { x : ℕ | (x : ℤ) + t ∈ A seq_n (λ i => seq_a i - t) } := by
  ext x
  simp [A]

/--
Finite modification lemma: changing finitely many residues doesn't affect existence of density.
-/
lemma finite_modification (seq_n seq_n' : ℕ → ℕ) (seq_a seq_a' : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n)
    (hpos' : ∀ i, 0 < seq_n' i) (hmono' : StrictMono seq_n')
    (hfin : ∀ᶠ i in atTop, seq_n i = seq_n' i ∧ seq_a i = seq_a' i) :
    (∃ d, HasLogDensity (A seq_n seq_a) d) ↔ (∃ d, HasLogDensity (A seq_n' seq_a') d) := by
  sorry

/--
If the answer is True: need to construct density for all sequences.
Strategy: use the tail-bound lemma to show the limit exists via Cauchy criterion.
-/
lemma universal_from_tail_bound :
    (∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
      CauchySeq (fun N : ℕ => ((∑ k in Finset.filter (λ k => k ∈ A seq_n seq_a) (Finset.Icc 1 N), (k : ℝ)⁻¹) : ℝ) / Real.log (N : ℝ))) →
    UniversalStatement := by
  intro h_cauchy seq_n seq_a hpos hmono
  have h_cau := h_cauchy seq_n seq_a hpos hmono
  have h_complete : ∀ (x : ℕ → ℝ), CauchySeq x → ∃ d, Tendsto x atTop (𝓝 d) := by
    intro x hx
    have h_cauchy_real : CauchySeq x := hx
    -- ℝ is complete
    rcases cauchy_iff.mp h_cauchy_real with ⟨h⟩
    sorry
  sorry

-- EVOLVE-BLOCK-END

/--
Erdős Problem 25: does the logarithmic density of A always exist?
-/
@[research_open]
theorem erdos_25 :
    True ↔ UniversalStatement := by
  constructor
  · intro _
    -- EVOLVE-BLOCK-START
    -- Attempt 1: try to prove UniversalStatement directly
    -- Attempt 2: construct a counterexample (answer = False)
    -- For now, we try the direct approach
    sorry
    -- EVOLVE-BLOCK-END
  · intro h
    trivial

end Erdos25
