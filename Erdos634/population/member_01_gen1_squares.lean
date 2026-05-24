import Mathlib

open Set Finset
open scoped Real

/-
  Population Member 01: Strategy = Squares via grid dissection
  Approach: Show squares work by dividing an equilateral triangle
    into k² congruent smaller equilateral triangles via a k×k grid.
  Rating (initial): Elo 1200
-/

namespace Erdos634

structure Triangle where
  A : ℝ × ℝ
  B : ℝ × ℝ
  C : ℝ × ℝ
  nondegenerate : (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) ≠ 0

def distSq (P Q : ℝ × ℝ) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

def Congruent (T₁ T₂ : Triangle) : Prop :=
  (distSq T₁.A T₁.B = distSq T₂.A T₂.B ∧ distSq T₁.B T₁.C = distSq T₂.B T₂.C ∧ distSq T₁.C T₁.A = distSq T₂.C T₂.A) ∨
  (distSq T₁.A T₁.B = distSq T₂.B T₂.C ∧ distSq T₁.B T₁.C = distSq T₂.C T₂.A ∧ distSq T₁.C T₁.A = distSq T₂.A T₂.B) ∨
  (distSq T₁.A T₁.B = distSq T₂.C T₂.A ∧ distSq T₁.B T₁.C = distSq T₂.A T₂.B ∧ distSq T₁.C T₁.A = distSq T₂.B T₂.C)

-- EVOLVE-BLOCK-START

/-- An equilateral triangle with vertices at (0,0), (1,0), (1/2, √3/2). -/
def equilateral : Triangle where
  A := (0, 0)
  B := (1, 0)
  C := (1/2, Real.sqrt 3 / 2)
  nondegenerate := by
    norm_num [Real.sqrt]
    ring

/-- Divide the equilateral triangle into a k×k grid of smaller congruent
    equilateral triangles. Each small triangle has side length 1/k. -/
def grid_triangles (k : ℕ) : Finset Triangle :=
  -- For each i,j in a k×k grid, produce two small triangles per cell
  (Finset.product (Finset.range k) (Finset.range k)).image (λ ⟨i, j⟩ =>
    { A := ((i : ℝ) / k, (j : ℝ) * Real.sqrt 3 / (2 * k))
      B := (((i+1 : ℕ) : ℝ) / k, (j : ℝ) * Real.sqrt 3 / (2 * k))
      C := (((2*i+1 : ℕ) : ℝ) / (2*k), ((j+1 : ℕ) : ℝ) * Real.sqrt 3 / (2 * k))
      nondegenerate := by
        sorry })

-- EVOLVE-BLOCK-END

end Erdos634
