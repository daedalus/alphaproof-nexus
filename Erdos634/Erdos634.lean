import Mathlib

open Set Finset
open scoped Real

/-
  Erdős Problem #634 — Triangle Tilings

  Find all n such that there is at least one triangle
  which can be cut into n congruent triangles.

  Status (2026-05-24): OPEN, $25
  https://erdosproblems.com/634

  Known: all squares work; 2n², 3n², 6n², n²+m² work.
  7 and 11 do not work. Unknown whether 19 works.
-/

namespace Erdos634

/-- A triangle is defined by three non-collinear points in the plane. -/
structure Triangle where
  A : ℝ × ℝ
  B : ℝ × ℝ
  C : ℝ × ℝ
  nondegenerate : (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) ≠ 0

/-- Squared distance between two points. -/
def distSq (P Q : ℝ × ℝ) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/-- Two triangles are congruent if their three side lengths (squared) match pairwise. -/
def Congruent (T₁ T₂ : Triangle) : Prop :=
  (distSq T₁.A T₁.B = distSq T₂.A T₂.B ∧ distSq T₁.B T₁.C = distSq T₂.B T₂.C ∧ distSq T₁.C T₁.A = distSq T₂.C T₂.A) ∨
  (distSq T₁.A T₁.B = distSq T₂.B T₂.C ∧ distSq T₁.B T₁.C = distSq T₂.C T₂.A ∧ distSq T₁.C T₁.A = distSq T₂.A T₂.B) ∨
  (distSq T₁.A T₁.B = distSq T₂.C T₂.A ∧ distSq T₁.B T₁.C = distSq T₂.A T₂.B ∧ distSq T₁.C T₁.A = distSq T₂.B T₂.C)

/-- A finite set of triangles tiles a given triangle T if they are pairwise
    interior-disjoint, each is congruent to a fixed shape, and their union is T.

    We simplify: a Finset of triangles covers T and each is congruent to shape S. -/
structure Tiling (T S : Triangle) where
  pieces : Finset Triangle
  card_eq : pieces.card = n
  all_congruent : ∀ t ∈ pieces, Congruent t S
  -- Additional constraints (disjointness, covering) omitted for brevity

/-- The property that there exists a triangle tileable by n congruent triangles. -/
def TriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle) (tiling : Tiling T S n), True

/-- The known set of n for which a tiling exists (superset of actual answers). -/
def KnownTilable : Set ℕ :=
  { n | ∃ (a b : ℕ), n = a^2 + b^2 ∨ n = 2*a^2 ∨ n = 3*a^2 ∨ n = 6*a^2 ∨ n = a^2 }

lemma squares_work (k : ℕ) : TriangleTilable (k^2) := by
  sorry

lemma sum_of_squares_work (a b : ℕ) : TriangleTilable (a^2 + b^2) := by
  sorry

-- EVOLVE-BLOCK-START

/-- The main conjecture: characterize all tilable n.
    The full set is unknown; this is a placeholder for partial progress. -/
@[research_open]
theorem erdos634_classification : Set ℕ := by
  -- The conjectured answer (or partial characterization)
  sorry

-- EVOLVE-BLOCK-END

end Erdos634
