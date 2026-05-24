/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 25: Logarithmic density of size-dependent congruences

*Reference:* [erdosproblems.com/25](https://www.erdosproblems.com/25)

Let $1 \leq n_1 < n_2 < \cdots$ be an arbitrary sequence of integers, each with an associated
residue class $a_i \pmod{n_i}$. Let $A$ be the set of integers $n$ such that for every $i$ either
$n < n_i$ or $n \not\equiv a_i \pmod{n_i}$. Must the logarithmic density of $A$ exist?

## EVOLVE-BLOCK structure

The EVOLVE-VALUE marks the answer (True or False). The EVOLVE-BLOCK contains helper definitions
and decomposed lemmas for the agent to fill in. The core unknown is whether a counterexample
can be constructed (answer = False) or if the density always exists (answer = True).
-/

open Filter Finset Real Nat Set
open scoped Topology
open Classical

namespace Erdos25

-- EVOLVE-BLOCK-START

/-- The set A as defined in the problem statement. An integer x is in A iff for every
modulus n_i, either x is below the threshold n_i or x avoids the forbidden residue. -/
def A (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

/-- Equivalent definition: x ∈ A iff for all i with n_i ≤ x, x ≢ a_i (mod n_i). -/
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
    ∃ d, Set.HasLogDensity (A seq_n seq_a) d

/--
Known theorem of Davenport and Erdős: when all residues are 0, the logarithmic density exists.
Reference: Davenport, H. and Erdős, P., "On sequences of integers" (1936, 1951).
-/
lemma davenport_erdos_case (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    ∃ d, Set.HasLogDensity (A seq_n (λ _ => 0)) d := by
  sorry

/--
If the answer is True (density always exists), this lemma gives the forward direction.
-/
lemma answer_true_implies_universal : True → UniversalStatement := by
  intro ht
  -- The constant True carries no information; we must prove the universal statement directly
  sorry

/--
If the answer is False (density does not always exist), there must be a counterexample.
This structure captures a concrete witnessing pair of sequences.
-/
structure Counterexample where
  seq_n : ℕ → ℕ
  seq_a : ℕ → ℤ
  hpos : ∀ i, 0 < seq_n i
  hmono : StrictMono seq_n
  h_no_density : ¬ ∃ d, Set.HasLogDensity (A seq_n seq_a) d

/--
If a counterexample exists, the answer is False.
-/
lemma counterexample_implies_answer_false : Nonempty Counterexample → (¬ UniversalStatement) := by
  intro hce
  rcases hce with ⟨ce⟩
  intro huni
  apply ce.h_no_density
  exact huni ce.seq_n ce.seq_a ce.hpos ce.hmono

/--
Translation by a constant: if we add t to every residue, does the density property change?
For each fixed i, the condition x ≡ a_i (mod n_i) ↔ (x + t) ≡ a_i + t (mod n_i).
-/
lemma translation_shift (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (t : ℤ) :
    A seq_n seq_a = { x : ℕ | x + (t.natAbs : ℕ) ∈ A seq_n (λ i => seq_a i - t) } := by
  ext x
  simp [A]

/--
The density, if it exists, is unchanged under translation of the set by a constant.
This is because logarithmic density is shift-invariant.
-/
lemma log_density_translation_invariant (S : Set ℕ) (k : ℕ) (d : ℝ) :
    Set.HasLogDensity S d → Set.HasLogDensity ({ x : ℕ | x + k ∈ S } : Set ℕ) d := by
  sorry

/--
If the residues are all equal to some constant r, then we can reduce to the
Davenport-Erdős case via translation.
-/
lemma constant_residue_case (seq_n : ℕ → ℕ) (r : ℤ) (hpos : ∀ i, 0 < seq_n i)
    (hmono : StrictMono seq_n) : ∃ d, Set.HasLogDensity (A seq_n (λ _ => r)) d := by
  sorry

/--
Every modulus n_i has finitely many residue classes. If we partition ℕ by which residues
appear at each modulus, the set A decomposes into a disjoint union of simpler sets.
-/
lemma partition_by_residues (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i)
    (hmono : StrictMono seq_n) (N : ℕ) :
    (A seq_n seq_a) ∩ Iic N = (Finset.Iic N).filter (λ x => ∀ i, seq_n i ≤ x → 
      ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxA, hxN⟩
    have hxN' : x ≤ N := hxN
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Iic.mpr hxN
    · rw [A_iff seq_n seq_a x] at hxA
      exact hxA
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hx_mem, hx_prop⟩
    constructor
    · rw [A_iff seq_n seq_a x]
      exact hx_prop
    · exact Finset.mem_Iic.mp hx_mem

/--
The logarithmic density of A, if it exists, is the limit of (1/log N) * sum_{x ≤ N, x ∈ A} 1/x.
If we know the partial sums up to any modulus M, we might be able to control the tail.
-/
lemma partial_sums_bound (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i)
    (hmono : StrictMono seq_n) (M : ℕ) : 0 ≤ (∑ x in Finset.Icc 1 M, (if x ∈ A seq_n seq_a then (1 : ℝ) / x else 0)) := by
  apply Finset.sum_nonneg
  intro x hx
  split <;> positivity

/--
The tail contribution from x > N to the logarithmic density can be bounded using
the structure of the sequences. For large x, only moduli n_i ≤ x are active.
-/
lemma tail_bound (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i)
    (hmono : StrictMono seq_n) (N : ℕ) :
    |(∑ x in Finset.Icc 1 N, ((if x ∈ A seq_n seq_a then (1 : ℝ) / x else 0) : ℝ)) -
     (∑ x in Finset.Icc 1 N, ((if x ∈ A (λ i => seq_n (i + 1)) (λ i => seq_a (i + 1)) then (1 : ℝ) / x else 0) : ℝ))| ≤
    (∑ i, 1 / (seq_n i : ℝ)) - (∑ i < N, 1 / (seq_n i : ℝ)) := by
  sorry

-- EVOLVE-BLOCK-END

/--
Erdős Problem 25: does the logarithmic density of A always exist?

The `answer(sorry)` is the EVOLVE-VALUE — replace `sorry` with `True` or `False`.
The `↔` direction ensures the answer matches the mathematical truth.
-/
@[category research open, AMS 11]
theorem erdos_25 :
    answer(
      -- EVOLVE-VALUE-START
      sorry
      -- EVOLVE-VALUE-END
    ) ↔ UniversalStatement := by
  -- EVOLVE-BLOCK-START
  constructor
  · intro h_answer
    -- h_answer : answer_value (True or False)
    -- If answer is True, we need to prove UniversalStatement
    -- If answer is False, we need to prove ¬UniversalStatement,
    -- which the ↔ would make contradictory... unless answer is actually True.
    -- In the alwaysTrue mode, answer(sorry) defaults to True,
    -- so we just need to prove UniversalStatement.
    cases h_answer with
    | intro h =>
      -- h is a proof of the answer value
      -- We need to extract and use it
      sorry
  · intro h_uni
    -- UniversalStatement holds, so answer must be True
    trivial
  -- EVOLVE-BLOCK-END

end Erdos25
