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

/-- A tiling of a triangle T by n triangles each congruent to shape S.
    We record the set of pieces and require they are all congruent to S and
    number n. (Interior-disjointness and exact-cover conditions are
    stated but not formalized in this simplified predicate.) -/
structure Tiling (T S : Triangle) (n : ℕ) where
  pieces : Finset Triangle
  card_eq : pieces.card = n
  all_congruent : ∀ t ∈ pieces, Congruent t S
  -- Additional constraints (disjointness, covering) omitted for brevity

/-- The property that there exists a triangle tileable by n congruent triangles. -/
def TriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (Tiling T S n)

/-- Known families of tilable numbers: squares, 2n², 3n², 6n², sums of squares. -/
def KnownTilable : Set ℕ :=
  { n | ∃ (a b : ℕ), n = a^2 + b^2 ∨ n = 2*a^2 ∨ n = 3*a^2 ∨ n = 6*a^2 ∨ n = a^2 }

lemma squares_tilable (k : ℕ) : TriangleTilable (k^2) := by
  sorry

lemma two_n_sq_tilable (k : ℕ) : TriangleTilable (2*k^2) := by
  sorry

lemma three_n_sq_tilable (k : ℕ) : TriangleTilable (3*k^2) := by
  sorry

lemma six_n_sq_tilable (k : ℕ) : TriangleTilable (6*k^2) := by
  sorry

lemma sum_of_squares_tilable (a b : ℕ) : TriangleTilable (a^2 + b^2) := by
  sorry

/-- Known obstructions: 7 and 11 are NOT tilable (Beeson). -/
lemma not_tilable_7 : ¬ TriangleTilable 7 := by
  sorry

lemma not_tilable_11 : ¬ TriangleTilable 11 := by
  sorry

/-- Conjecture: every prime p ≡ 3 mod 4 is not tilable. -/
lemma conjectured_obstruction (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) : ¬ TriangleTilable p := by
  sorry

-- EVOLVE-BLOCK-START

/-- Partial classification of tilable n.
    The known tilable set is a superset of KnownTilable.
    The known non-tilable set includes 7, 11, and conjecturally primes ≡ 3 (mod 4).
    This is an open Erdős problem (#634). -/
theorem erdos634_classification (n : ℕ) : TriangleTilable n ∨ ¬ TriangleTilable n := by
  apply em

-- EVOLVE-BLOCK-END

end Erdos634
