import Mathlib
open Set Finset
open scoped Real

namespace ErdosLib

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

/-- Signed area of a triangle (half of the determinant formula).
    Positive for counter-clockwise orientation. -/
noncomputable def signed_area (T : Triangle) : ℝ :=
  (T.A.1 * (T.B.2 - T.C.2) + T.B.1 * (T.C.2 - T.A.2) + T.C.1 * (T.A.2 - T.B.2)) / 2

/-- A tiling of a triangle T by n triangles each congruent to shape S. -/
structure Tiling (T S : Triangle) (n : ℕ) where
  pieces : Finset Triangle
  card_eq : pieces.card = n
  all_congruent : ∀ t ∈ pieces, Congruent t S

/-- The property that there exists a triangle tileable by n congruent triangles. -/
def TriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (Tiling T S n)

/-- The standard right triangle with legs 1 and √3 (a 30-60-90 triangle). -/
noncomputable def right_triangle : Triangle :=
  { A := (0, 0), B := (1, 0), C := (0, Real.sqrt 3)
    nondegenerate := by
      have hcalc : (0 : ℝ) * (0 - Real.sqrt 3) + 1 * (Real.sqrt 3 - 0) + 0 * (0 - 0) = Real.sqrt 3 := by ring
      rw [hcalc]
      positivity }

/-- The equilateral triangle with side length 1 (bottom-left corner at origin,
    base on the x-axis, apex above the midpoint). -/
noncomputable def equilateral : Triangle :=
  { A := (0, 0), B := (1, 0), C := (1/2, Real.sqrt 3 / 2)
    nondegenerate := by
      have hcalc : (0 : ℝ) * (0 - Real.sqrt 3 / 2) + 1 * (Real.sqrt 3 / 2 - 0) + (1/2) * (0 - 0) = Real.sqrt 3 / 2 := by ring
      rw [hcalc]
      positivity }

lemma signed_area_right_triangle : signed_area right_triangle = Real.sqrt 3 / 2 := by
  unfold signed_area right_triangle; ring

lemma signed_area_equilateral : signed_area equilateral = Real.sqrt 3 / 4 := by
  unfold signed_area equilateral; ring

end ErdosLib
