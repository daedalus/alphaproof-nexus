import Mathlib
import ErdosLib.Density

/-!
# Problem Structure

Reusable structure for Erdős open problems:
- Answer (unknown / True / False)
- `research_open` attribute
- Universal statement pattern (parameterized by density predicate)
-/

open Lean Elab

namespace ErdosLib

variable (densityPred : Set ℕ → ℝ → Prop)

/-- The current knowledge state of an Erdős problem. -/
inductive Answer : Type where
  | unknown
  | true
  | false

/-- Decoration for open problems: marks a theorem as an open Erdős problem. -/
@[nat]
private def attr_research_open : Name := `research_open

initialize registerBuiltinAttribute {
  name := attr_research_open
  descr := "Marks a theorem as an open Erdős problem"
  add := fun src kind _ => match src, kind with
    | .decl declName, AttributeKind.global => do
      Library.addDeclAPIInfo declName { extra := { "research_open" := "true" } }
    | _, _ => pure ()
  erase := fun _ => pure ()
}

/-- Build a set from sequences of moduli and residues.
    An integer x is in the set iff for every i,
    either x is below the threshold n_i or x avoids the forbidden residue. -/
def A_from_seqs (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

lemma mem_A_from_seqs_iff (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (x : ℕ) :
    x ∈ A_from_seqs seq_n seq_a ↔ ∀ i, seq_n i ≤ x → ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) := by
  dsimp [A_from_seqs]
  constructor
  · intro h i hi
    rcases h i with (hlt | hne)
    · exfalso; exact Nat.not_lt.mpr hi hlt
    · exact hne
  · intro h i
    by_cases hx : seq_n i ≤ x
    · right; exact h i hx
    · left; exact Nat.lt_of_not_ge hx

/-- Universal statement: for any sequences of moduli and residues,
    the set A (congruence-avoiding) has a density w.r.t. the given density predicate. -/
def UniversalStatement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, densityPred (A_from_seqs seq_n seq_a) d

/-- Universal statement for logarithmic density (Erdős #25). -/
def UniversalLogDensityStatement : Prop :=
  UniversalStatement HasLogDensity

/-- Universal statement for natural density (stronger assumption). -/
def UniversalNaturalDensityStatement : Prop :=
  UniversalStatement HasDensity

end ErdosLib
