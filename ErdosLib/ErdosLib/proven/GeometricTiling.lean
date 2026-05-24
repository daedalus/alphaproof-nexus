import Mathlib
open Set Finset
open scoped Real

namespace ErdosLib

/-- A point p is inside the closed triangle T if it can be written as a convex
    combination of T's vertices with non-negative coefficients summing to 1. -/
def point_in_triangle (p : ℝ × ℝ) (T : Triangle) : Prop :=
  ∃ (α β γ : ℝ), α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ α + β + γ = 1 ∧
    p.1 = α * T.A.1 + β * T.B.1 + γ * T.C.1 ∧
    p.2 = α * T.A.2 + β * T.B.2 + γ * T.C.2

/-- A point p is in the interior of closed triangle T if all barycentric
    coefficients are strictly positive. -/
def point_in_interior (p : ℝ × ℝ) (T : Triangle) : Prop :=
  ∃ (α β γ : ℝ), α > 0 ∧ β > 0 ∧ γ > 0 ∧ α + β + γ = 1 ∧
    p.1 = α * T.A.1 + β * T.B.1 + γ * T.C.1 ∧
    p.2 = α * T.A.2 + β * T.B.2 + γ * T.C.2

/-- A set of triangles is pairwise interior-disjoint if no two distinct triangles
    share an interior point. -/
def PairwiseInteriorDisjoint (pieces : Finset Triangle) : Prop :=
  ∀ t₁ ∈ pieces, ∀ t₂ ∈ pieces, t₁ ≠ t₂ → ¬∃ p, point_in_interior p t₁ ∧ point_in_interior p t₂

/-- A geometric tiling adds three constraints to the weak Tiling:
    • `subset_T`: all piece vertices lie inside T (via point_in_triangle)
    • `cover_T`: all three vertices of T are among the piece vertices
    • `pairwise_disjoint`: piece interiors are disjoint
    Together these imply the pieces form a proper triangulation of T. -/
structure GeometricTiling (T S : Triangle) (n : ℕ) where
  pieces : Finset Triangle
  card_eq : pieces.card = n
  all_congruent : ∀ t ∈ pieces, Congruent t S
  area_eq : Finset.sum pieces (λ t => signed_area t) = signed_area T
  subset_T : ∀ t ∈ pieces, point_in_triangle t.A T ∧ point_in_triangle t.B T ∧ point_in_triangle t.C T
  cover_T : T.A ∈ Finset.biUnion pieces (λ t => {t.A, t.B, t.C}) ∧
            T.B ∈ Finset.biUnion pieces (λ t => {t.A, t.B, t.C}) ∧
            T.C ∈ Finset.biUnion pieces (λ t => {t.A, t.B, t.C})
  pairwise_disjoint : PairwiseInteriorDisjoint pieces

/-- The property that a geometric tiling exists. -/
def GeometricTriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (GeometricTiling T S n)

lemma geometric_implies_weak (n : ℕ) (h : GeometricTriangleTilable n) : TriangleTilable n := by
  rcases h with ⟨T, S, ⟨g⟩⟩
  refine ⟨T, S, ⟨{
    pieces := g.pieces
    card_eq := g.card_eq
    all_congruent := g.all_congruent
    area_eq := g.area_eq
  }⟩⟩

end ErdosLib
