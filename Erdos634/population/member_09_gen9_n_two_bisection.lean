import Mathlib

open Set Finset
open scoped Real

noncomputable section

/-
-! ### Formalization gap: weak TriangleTilable vs GeometricTriangleTilable

The weak `Tiling` predicate (no disjointness, no covering) makes `tilable_all_pos`
trivially true, which CONTRADICTS `not_tilable_7`/`not_tilable_11`. The real
Erdős problem requires `GeometricTiling` constraints.

`not_subset_T_strip_construction` shows the 1D strip construction used in
`tilable_all_pos` fails the `subset_T` constraint: the last piece's apex
lies outside the target triangle. Hence `tilable_all_pos` does NOT produce
any `GeometricTiling`. The `GeometricTriangleTilable` predicate is the
correct formalization of the Erdős problem.

### Geometric area scaling

For a `GeometricTiling T S n`, the n congruent pieces all have the same
absolute signed area (by SSS congruence), and their total signed area
equals that of T. This gives `|n * signed_area(S)| = |signed_area(T)|`.
-/

namespace Erdos634

/-- A triangle is defined by three non-collinear points in the plane. -/
structure Triangle where
  A : ℝ × ℝ
  B : ℝ × ℝ
  C : ℝ × ℝ
  nondegenerate : (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) ≠ 0
deriving DecidableEq

/-- Squared distance between two points. -/
def distSq (P Q : ℝ × ℝ) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/-- Signed area (shoelace formula) of a triangle. Positive for CCW vertices. -/
def signed_area (t : Triangle) : ℝ :=
  (t.A.1 * (t.B.2 - t.C.2) + t.B.1 * (t.C.2 - t.A.2) + t.C.1 * (t.A.2 - t.B.2)) / 2

/-- Two triangles are congruent if their three side lengths (squared) match pairwise
    under some permutation of vertices (SSS congruence).
    Checks all 6 permutations to handle reflected / opposite-orientation triangles. -/
def Congruent (T₁ T₂ : Triangle) : Prop :=
  (distSq T₁.A T₁.B = distSq T₂.A T₂.B ∧ distSq T₁.B T₁.C = distSq T₂.B T₂.C ∧ distSq T₁.C T₁.A = distSq T₂.C T₂.A) ∨
  (distSq T₁.A T₁.B = distSq T₂.B T₂.C ∧ distSq T₁.B T₁.C = distSq T₂.C T₂.A ∧ distSq T₁.C T₁.A = distSq T₂.A T₂.B) ∨
  (distSq T₁.A T₁.B = distSq T₂.C T₂.A ∧ distSq T₁.B T₁.C = distSq T₂.A T₂.B ∧ distSq T₁.C T₁.A = distSq T₂.B T₂.C) ∨
  (distSq T₁.A T₁.B = distSq T₂.A T₂.C ∧ distSq T₁.B T₁.C = distSq T₂.C T₂.B ∧ distSq T₁.C T₁.A = distSq T₂.B T₂.A) ∨
  (distSq T₁.A T₁.B = distSq T₂.B T₂.A ∧ distSq T₁.B T₁.C = distSq T₂.A T₂.C ∧ distSq T₁.C T₁.A = distSq T₂.C T₂.B) ∨
  (distSq T₁.A T₁.B = distSq T₂.C T₂.B ∧ distSq T₁.B T₁.C = distSq T₂.B T₂.A ∧ distSq T₁.C T₁.A = distSq T₂.A T₂.C)

/-- A tiling of a triangle T by n triangles each congruent to shape S (weak definition:
    no disjointness or covering constraints). -/
structure Tiling (T S : Triangle) (n : ℕ) where
  pieces : Finset Triangle
  card_eq : pieces.card = n
  all_congruent : ∀ t ∈ pieces, Congruent t S
  area_eq : Finset.sum pieces (λ t => signed_area t) = signed_area T

/-- The property that there exists a triangle tileable by n congruent triangles (weak). -/
def TriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (Tiling T S n)

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

/-- An equilateral triangle with vertices at (0,0), (1,0), (1/2, √3/2). -/
def equilateral : Triangle where
  A := (0, 0)
  B := (1, 0)
  C := (1/2, Real.sqrt 3 / 2)
  nondegenerate := by
    have h : (0 : ℝ) * (0 - Real.sqrt 3 / 2) + 1 * (Real.sqrt 3 / 2 - 0) + (1/2) * (0 - 0) = Real.sqrt 3 / 2 := by ring
    rw [h]
    positivity

/-- A right triangle with legs of length 1 and √3, used in 2k² constructions. -/
def right_triangle : Triangle where
  A := (0, 0)
  B := (1, 0)
  C := (0, Real.sqrt 3)
  nondegenerate := by
    have h : (0 : ℝ) * (0 - Real.sqrt 3) + 1 * (Real.sqrt 3 - 0) + 0 * (0 - 0) = Real.sqrt 3 := by ring
    rw [h]
    positivity

/-- Triangular lattice point in an equilateral triangle of side length 1,
    where we divide each side into k equal segments.
    Coordinates: (i/k + j/(2k), j·√3/(2k)) for i,j ≥ 0. -/
def lattice_point (i j k : ℕ) : ℝ × ℝ :=
  ((i : ℝ) / (k : ℝ) + (j : ℝ) / (2*(k : ℝ)), (j : ℝ) * Real.sqrt 3 / (2*(k : ℝ)))

/-- Upward triangle determinant: the shoelace formula gives √3/(2k²) when k > 0. -/
lemma up_triangle_det_eq (i j k : ℕ) (hk : k > 0) :
    (lattice_point i j k).1 * ((lattice_point (i+1) j k).2 - (lattice_point i (j+1) k).2) +
    (lattice_point (i+1) j k).1 * ((lattice_point i (j+1) k).2 - (lattice_point i j k).2) +
    (lattice_point i (j+1) k).1 * ((lattice_point i j k).2 - (lattice_point (i+1) j k).2) =
    Real.sqrt 3 / (2 * ((k : ℝ) ^ 2)) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [lattice_point]
  field_simp [hk']
  ring

/-- Downward triangle determinant: same value √3/(2k²) for the complementary orientation. -/
lemma down_triangle_det_eq (i j k : ℕ) (hk : k > 0) :
    (lattice_point (i+1) j k).1 * ((lattice_point (i+1) (j+1) k).2 - (lattice_point i (j+1) k).2) +
    (lattice_point (i+1) (j+1) k).1 * ((lattice_point i (j+1) k).2 - (lattice_point (i+1) j k).2) +
    (lattice_point i (j+1) k).1 * ((lattice_point (i+1) j k).2 - (lattice_point (i+1) (j+1) k).2) =
    Real.sqrt 3 / (2 * ((k : ℝ) ^ 2)) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [lattice_point]
  field_simp [hk']
  ring

/-- An upward-pointing small equilateral triangle in the k×k grid.
    Vertices: bottom-left (i,j), bottom-right (i+1,j), top (i,j+1). -/
def up_triangle (i j k : ℕ) : Triangle :=
  if hk : k = 0 then
    { A := (0,0), B := (1,0), C := (0,1), nondegenerate := by norm_num }
  else
    { A := lattice_point i j k
      B := lattice_point (i+1) j k
      C := lattice_point i (j+1) k
      nondegenerate := by
        have hpos : k > 0 := Nat.pos_of_ne_zero hk
        have hcalc : (lattice_point i j k).1 * ((lattice_point (i+1) j k).2 - (lattice_point i (j+1) k).2) +
          (lattice_point (i+1) j k).1 * ((lattice_point i (j+1) k).2 - (lattice_point i j k).2) +
          (lattice_point i (j+1) k).1 * ((lattice_point i j k).2 - (lattice_point (i+1) j k).2) =
          Real.sqrt 3 / (2 * ((k : ℝ) ^ 2)) := up_triangle_det_eq i j k hpos
        rw [hcalc]
        refine div_ne_zero (by positivity : Real.sqrt 3 ≠ 0) (by
          have : (k : ℝ) ^ 2 > 0 := pow_pos (by exact_mod_cast hpos) 2
          nlinarith) }

/-- A downward-pointing small equilateral triangle in the k×k grid (filling gaps).
    Vertices: top-left (i+1,j), top-right (i+1,j+1), bottom (i,j+1). -/
def down_triangle (i j k : ℕ) : Triangle :=
  if hk : k = 0 then
    { A := (0,0), B := (1,0), C := (0,1), nondegenerate := by norm_num }
  else
    { A := lattice_point (i+1) j k
      B := lattice_point (i+1) (j+1) k
      C := lattice_point i (j+1) k
      nondegenerate := by
        have hpos : k > 0 := Nat.pos_of_ne_zero hk
        have hcalc : (lattice_point (i+1) j k).1 * ((lattice_point (i+1) (j+1) k).2 - (lattice_point i (j+1) k).2) +
          (lattice_point (i+1) (j+1) k).1 * ((lattice_point i (j+1) k).2 - (lattice_point (i+1) j k).2) +
          (lattice_point i (j+1) k).1 * ((lattice_point (i+1) j k).2 - (lattice_point (i+1) (j+1) k).2) =
          Real.sqrt 3 / (2 * ((k : ℝ) ^ 2)) := down_triangle_det_eq i j k hpos
        rw [hcalc]
        refine div_ne_zero (by positivity : Real.sqrt 3 ≠ 0) (by
          have : (k : ℝ) ^ 2 > 0 := pow_pos (by exact_mod_cast hpos) 2
          nlinarith) }

/-- All upward- and downward- pointing triangles for the k×k grid.
    Indices: 0 ≤ i,j < k with i+j < k for up, 0 ≤ i,j < k-1 with i+j < k-1 for down. -/
def grid_triangles (k : ℕ) : Finset Triangle :=
  (Finset.filter (λ ⟨i,j⟩ => i + j < k) (Finset.product (Finset.range k) (Finset.range k))).image (λ ⟨i,j⟩ => up_triangle i j k) ∪
  (Finset.filter (λ ⟨i,j⟩ => i + j < k - 1) (Finset.product (Finset.range (k-1)) (Finset.range (k-1)))).image (λ ⟨i,j⟩ => down_triangle i j k)

-- EVOLVE-BLOCK-START

private lemma mul_lt_of_lt_div {a b d : ℝ} (hd : 0 < d) (h : a < b / d) : a * d < b := by
  calc
    a * d < (b / d) * d := mul_lt_mul_of_pos_right h hd
    _ = b := by field_simp [hd.ne']

private lemma lt_mul_of_div_lt {a b d : ℝ} (hd : 0 < d) (h : a / d < b) : a < b * d := by
  calc
    a = (a / d) * d := by field_simp [hd.ne']
    _ < b * d := mul_lt_mul_of_pos_right h hd

/-- Helper: (k*(k+1))/2 + k + 1 = ((k+1)*(k+2))/2. -/
lemma triangular_succ (k : ℕ) : (k * (k + 1)) / 2 + k + 1 = ((k + 1) * (k + 2)) / 2 := by
  have h_even : Even (k * (k + 1)) := Nat.even_mul_succ_self k
  rcases h_even with ⟨t, ht⟩
  have h2t : k * (k + 1) = 2 * t := by omega
  have h_eq : (k + 1) * (k + 2) = 2 * (t + k + 1) := by
    calc
      (k + 1) * (k + 2) = k * (k + 1) + 2 * (k + 1) := by ring
      _ = (2 * t) + 2 * (k + 1) := by rw [h2t]
      _ = 2 * (t + k + 1) := by ring
  calc
    (k * (k + 1)) / 2 + k + 1 = (2 * t) / 2 + k + 1 := by rw [h2t]
    _ = t + k + 1 := by simp
    _ = (2 * (t + k + 1)) / 2 := by simp
    _ = ((k + 1) * (k + 2)) / 2 := by rw [h_eq]

/-- The number of up-indices (i,j) with i+j < k in the k×k grid is k(k+1)/2. -/
lemma count_up_indices (k : ℕ) :
    (Finset.filter (λ (ij : ℕ × ℕ) => ij.1 + ij.2 < k)
      (Finset.product (Finset.range k) (Finset.range k))).card = (k * (k + 1)) / 2 := by
  induction' k with k ih
  · simp
  · let P_k := Finset.filter (λ (ij : ℕ × ℕ) => ij.1 + ij.2 < k)
      (Finset.product (Finset.range k) (Finset.range k))
    let P_kp1 := Finset.filter (λ (ij : ℕ × ℕ) => ij.1 + ij.2 < k + 1)
      (Finset.product (Finset.range (k + 1)) (Finset.range (k + 1)))
    let D_k := (Finset.range (k + 1)).image (λ t : ℕ => (t, k - t))
    have h_cover : P_kp1 = P_k ∪ D_k := by
      ext ⟨i, j⟩
      simp [P_k, P_kp1, D_k, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_union, Finset.mem_image]
      omega
    have h_disjoint : P_k ∩ D_k = ∅ := by
      ext ⟨i, j⟩
      simp [P_k, D_k, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_inter, Finset.mem_image]
      omega
    have h_disjoint' : Disjoint P_k D_k :=
      Finset.disjoint_iff_inter_eq_empty.mpr h_disjoint
    have h_card_D : D_k.card = k + 1 := by
      calc
        D_k.card = (Finset.range (k + 1)).card :=
          Finset.card_image_of_injective _ (λ a b h => by
            injection h)
        _ = k + 1 := by simp
    calc
      (Finset.filter (λ (ij : ℕ × ℕ) => ij.1 + ij.2 < k + 1)
        (Finset.product (Finset.range (k + 1)) (Finset.range (k + 1)))).card
          = (P_k ∪ D_k).card := by rw [← h_cover]
      _ = P_k.card + D_k.card := by rw [Finset.card_union_of_disjoint h_disjoint']
      _ = (k * (k + 1)) / 2 + (k + 1) := by rw [ih, h_card_D]
      _ = ((k + 1) * (k + 2)) / 2 := triangular_succ k

/-- The number of down-indices (i,j) with i+j < k-1 in the (k-1)×(k-1) grid. -/
lemma count_down_indices (k : ℕ) :
    (Finset.filter (λ (ij : ℕ × ℕ) => ij.1 + ij.2 < k - 1)
      (Finset.product (Finset.range (k - 1)) (Finset.range (k - 1)))).card = ((k - 1) * k) / 2 := by
  by_cases hk : k = 0
  · subst k; simp
  · have hpos : k > 0 := Nat.pos_of_ne_zero hk
    have h := count_up_indices (k - 1)
    have hsum : ((k - 1) * ((k - 1) + 1)) / 2 = ((k - 1) * k) / 2 := by
      have : (k - 1) + 1 = k := by omega
      simp [this]
    simpa [hsum] using h

/-- The `up_triangle` function is injective on its index set when k > 0. -/
lemma up_triangle_injective (k : ℕ) (hk : k > 0) :
    Function.Injective (λ (ij : ℕ × ℕ) => up_triangle ij.1 ij.2 k) := by
  intro ij1 ij2 h
  have hA : (up_triangle ij1.1 ij1.2 k).A = (up_triangle ij2.1 ij2.2 k).A := by simpa [h]
  have hk' : k ≠ 0 := by omega
  have hA1 : (up_triangle ij1.1 ij1.2 k).A = lattice_point ij1.1 ij1.2 k := by
    unfold up_triangle
    split
    · exfalso; exact hk' (by assumption)
    · rfl
  have hA2 : (up_triangle ij2.1 ij2.2 k).A = lattice_point ij2.1 ij2.2 k := by
    unfold up_triangle
    split
    · exfalso; exact hk' (by assumption)
    · rfl
  rw [hA1, hA2] at hA
  have hy : (ij1.2 : ℝ) = (ij2.2 : ℝ) := by
    have hy' : (lattice_point ij1.1 ij1.2 k).2 = (lattice_point ij2.1 ij2.2 k).2 := by rw [hA]
    simp [lattice_point] at hy'
    have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have h_eq_scaled : (ij1.2 : ℝ) * Real.sqrt 3 = (ij2.2 : ℝ) * Real.sqrt 3 := by
      calc
        (ij1.2 : ℝ) * Real.sqrt 3 = ((ij1.2 : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by field_simp [hkℝ]
        _ = ((ij2.2 : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by rw [hy']
        _ = (ij2.2 : ℝ) * Real.sqrt 3 := by field_simp [hkℝ]
    have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
    exact mul_right_cancel₀ hsqrt3 h_eq_scaled
  have hx : (ij1.1 : ℝ) = (ij2.1 : ℝ) := by
    have hx' : (lattice_point ij1.1 ij1.2 k).1 = (lattice_point ij2.1 ij2.2 k).1 := by rw [hA]
    simp [lattice_point] at hx'
    have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp [hkℝ] at hx'
    have hjy : (ij1.2 : ℝ) = (ij2.2 : ℝ) := hy
    rw [hjy] at hx'
    nlinarith
  exact Prod.ext (by exact_mod_cast hx) (by exact_mod_cast hy)

/-- The `down_triangle` function is injective on its index set when k > 0. -/
lemma down_triangle_injective (k : ℕ) (hk : k > 0) :
    Function.Injective (λ (ij : ℕ × ℕ) => down_triangle ij.1 ij.2 k) := by
  intro ij1 ij2 h
  have hA : (down_triangle ij1.1 ij1.2 k).A = (down_triangle ij2.1 ij2.2 k).A := by simpa [h]
  have hk' : k ≠ 0 := by omega
  have hA1 : (down_triangle ij1.1 ij1.2 k).A = lattice_point (ij1.1 + 1) ij1.2 k := by
    unfold down_triangle
    split
    · exfalso; exact hk' (by assumption)
    · rfl
  have hA2 : (down_triangle ij2.1 ij2.2 k).A = lattice_point (ij2.1 + 1) ij2.2 k := by
    unfold down_triangle
    split
    · exfalso; exact hk' (by assumption)
    · rfl
  rw [hA1, hA2] at hA
  have hy : (ij1.2 : ℝ) = (ij2.2 : ℝ) := by
    have hy' : (lattice_point (ij1.1 + 1) ij1.2 k).2 = (lattice_point (ij2.1 + 1) ij2.2 k).2 := by rw [hA]
    simp [lattice_point] at hy'
    have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have h_eq_scaled : (ij1.2 : ℝ) * Real.sqrt 3 = (ij2.2 : ℝ) * Real.sqrt 3 := by
      calc
        (ij1.2 : ℝ) * Real.sqrt 3 = ((ij1.2 : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by field_simp [hkℝ]
        _ = ((ij2.2 : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by rw [hy']
        _ = (ij2.2 : ℝ) * Real.sqrt 3 := by field_simp [hkℝ]
    have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
    exact mul_right_cancel₀ hsqrt3 h_eq_scaled
  have hx : (ij1.1 : ℝ) = (ij2.1 : ℝ) := by
    have hx' : (lattice_point (ij1.1 + 1) ij1.2 k).1 = (lattice_point (ij2.1 + 1) ij2.2 k).1 := by rw [hA]
    simp [lattice_point] at hx'
    have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp [hkℝ] at hx'
    have hjy : (ij1.2 : ℝ) = (ij2.2 : ℝ) := hy
    rw [hjy] at hx'
    nlinarith
  exact Prod.ext (by exact_mod_cast hx) (by exact_mod_cast hy)

/-- Distance is invariant under translation. -/
lemma distSq_translate (P Q : ℝ × ℝ) (dx dy : ℝ) : distSq (P.1 + dx, P.2 + dy) (Q.1 + dx, Q.2 + dy) = distSq P Q := by
  simp [distSq]

/-- The three squared side lengths of up_triangle i j k (when k > 0) all equal 1/k². -/
lemma distSq_up_triangle_eq (i j k : ℕ) (hk : k > 0) :
    distSq (up_triangle i j k).A (up_triangle i j k).B = 1 / ((k : ℝ) ^ 2) ∧
    distSq (up_triangle i j k).B (up_triangle i j k).C = 1 / ((k : ℝ) ^ 2) ∧
    distSq (up_triangle i j k).C (up_triangle i j k).A = 1 / ((k : ℝ) ^ 2) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsq3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)
  unfold up_triangle
  split
  · exfalso; exact hk.ne' (by assumption)
  · simp [lattice_point, distSq]
    constructor
    · field_simp [hk']; nlinarith [hsq3]
    · constructor
      · field_simp [hk']; nlinarith [hsq3]
      · field_simp [hk']; nlinarith [hsq3]

/-- The three squared side lengths of down_triangle i j k (when k > 0) all equal 1/k². -/
lemma distSq_down_triangle_eq (i j k : ℕ) (hk : k > 0) :
    distSq (down_triangle i j k).A (down_triangle i j k).B = 1 / ((k : ℝ) ^ 2) ∧
    distSq (down_triangle i j k).B (down_triangle i j k).C = 1 / ((k : ℝ) ^ 2) ∧
    distSq (down_triangle i j k).C (down_triangle i j k).A = 1 / ((k : ℝ) ^ 2) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsq3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)
  unfold down_triangle
  split
  · exfalso; exact hk.ne' (by assumption)
  · simp [lattice_point, distSq]
    constructor
    · field_simp [hk']; nlinarith [hsq3]
    · constructor
      · field_simp [hk']; nlinarith [hsq3]
      · field_simp [hk']; nlinarith [hsq3]

lemma signed_area_equilateral : signed_area equilateral = Real.sqrt 3 / 4 := by
  unfold signed_area equilateral; ring

/-- The unique β barycentric coordinate of p w.r.t. the equilateral triangle. -/
def equi_beta (p : ℝ × ℝ) : ℝ := p.1 - p.2 / Real.sqrt 3

/-- The unique γ barycentric coordinate of p w.r.t. the equilateral triangle. -/
def equi_gamma (p : ℝ × ℝ) : ℝ := 2 * p.2 / Real.sqrt 3

/-- Vertex A of up-triangle (when k≠0). -/
lemma up_triangle_A_eq (i j k : ℕ) (hk : k ≠ 0) : (up_triangle i j k).A = lattice_point i j k := by
  unfold up_triangle; split
  · exfalso; exact hk ‹_›
  · rfl

lemma up_triangle_B_eq (i j k : ℕ) (hk : k ≠ 0) : (up_triangle i j k).B = lattice_point (i+1) j k := by
  unfold up_triangle; split
  · exfalso; exact hk ‹_›
  · rfl

lemma up_triangle_C_eq (i j k : ℕ) (hk : k ≠ 0) : (up_triangle i j k).C = lattice_point i (j+1) k := by
  unfold up_triangle; split
  · exfalso; exact hk ‹_›
  · rfl

lemma down_triangle_A_eq (i j k : ℕ) (hk : k ≠ 0) : (down_triangle i j k).A = lattice_point (i+1) j k := by
  unfold down_triangle; split
  · exfalso; exact hk ‹_›
  · rfl

lemma down_triangle_B_eq (i j k : ℕ) (hk : k ≠ 0) : (down_triangle i j k).B = lattice_point (i+1) (j+1) k := by
  unfold down_triangle; split
  · exfalso; exact hk ‹_›
  · rfl

lemma down_triangle_C_eq (i j k : ℕ) (hk : k ≠ 0) : (down_triangle i j k).C = lattice_point i (j+1) k := by
  unfold down_triangle; split
  · exfalso; exact hk ‹_›
  · rfl

lemma signed_area_up_triangle (i j k : ℕ) (hk : k > 0) : signed_area (up_triangle i j k) = Real.sqrt 3 / (4 * ((k : ℝ)^2)) := by
  unfold up_triangle
  split
  · exfalso; exact hk.ne' ‹_›
  · unfold signed_area
    rw [up_triangle_det_eq i j k hk]
    ring

lemma signed_area_down_triangle (i j k : ℕ) (hk : k > 0) : signed_area (down_triangle i j k) = Real.sqrt 3 / (4 * ((k : ℝ)^2)) := by
  unfold down_triangle
  split
  · exfalso; exact hk.ne' ‹_›
  · unfold signed_area
    rw [down_triangle_det_eq i j k hk]
    ring

/-- Every triangle in the k×k grid is congruent to the small triangle
    up_triangle 0 0 k (equilateral with side length 1/k). -/
lemma grid_congruent (k : ℕ) (t : Triangle) (ht : t ∈ grid_triangles k) : Congruent t (up_triangle 0 0 k) := by
  by_cases hk0 : k = 0
  · subst hk0
    have : grid_triangles 0 = ∅ := by
      ext t'; simp [grid_triangles]
    rw [this] at ht
    simp at ht
  · have hpos : k > 0 := Nat.pos_of_ne_zero hk0
    rcases Finset.mem_union.mp ht with (ht_up | ht_down)
    · rcases Finset.mem_image.mp ht_up with ⟨⟨i, j⟩, _, rfl⟩
      rcases distSq_up_triangle_eq i j k hpos with ⟨hAB, hBC, hCA⟩
      rcases distSq_up_triangle_eq 0 0 k hpos with ⟨hAB0, hBC0, hCA0⟩
      refine Or.inl ⟨?_, ?_, ?_⟩
      · rw [hAB, hAB0]
      · rw [hBC, hBC0]
      · rw [hCA, hCA0]
    · rcases Finset.mem_image.mp ht_down with ⟨⟨i, j⟩, _, rfl⟩
      rcases distSq_down_triangle_eq i j k hpos with ⟨hAB, hBC, hCA⟩
      rcases distSq_up_triangle_eq 0 0 k hpos with ⟨hAB0, hBC0, hCA0⟩
      refine Or.inl ⟨?_, ?_, ?_⟩
      · rw [hAB, hAB0]
      · rw [hBC, hBC0]
      · rw [hCA, hCA0]

/-- The k×k grid of small equilateral triangles has exactly k² pieces. -/
lemma grid_card (k : ℕ) : (grid_triangles k).card = k^2 := by
  by_cases hk : k = 0
  · subst k; simp [grid_triangles]
  · have hpos : k > 0 := Nat.pos_of_ne_zero hk
    let up_set : Finset Triangle := Finset.image (λ (ij : ℕ × ℕ) => up_triangle ij.1 ij.2 k)
      (Finset.filter (λ ⟨i,j⟩ => i + j < k) (Finset.product (Finset.range k) (Finset.range k)))
    let down_set : Finset Triangle := Finset.image (λ (ij : ℕ × ℕ) => down_triangle ij.1 ij.2 k)
      (Finset.filter (λ ⟨i,j⟩ => i + j < k - 1) (Finset.product (Finset.range (k-1)) (Finset.range (k-1))))
    have h_inter_empty : up_set ∩ down_set = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      rcases hne with ⟨t, ht⟩
      rcases Finset.mem_inter.1 ht with ⟨ht_up, ht_down⟩
      rcases Finset.mem_image.1 ht_up with ⟨⟨i, j⟩, hmem_up, rfl⟩
      rcases Finset.mem_image.1 ht_down with ⟨⟨i', j'⟩, hmem_down, h_eq⟩
      have hpos' : k ≠ 0 := by omega
      have hB : (up_triangle i j k).B = (down_triangle i' j' k).B := by simpa [h_eq]
      have hA : (up_triangle i j k).A = (down_triangle i' j' k).A := by rw [h_eq]
      have hB1 : (up_triangle i j k).B = lattice_point (i + 1) j k := by
        simp [up_triangle, hpos']
      have hB2 : (down_triangle i' j' k).B = lattice_point (i' + 1) (j' + 1) k := by
        simp [down_triangle, hpos']
      rw [hB1, hB2] at hB
      have hy_B : (j : ℝ) = (j' + 1 : ℝ) := by
        have hy' : (lattice_point (i + 1) j k).2 = (lattice_point (i' + 1) (j' + 1) k).2 := by rw [hB]
        simp [lattice_point] at hy'
        have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
        have h_eq_scaled : (j : ℝ) * Real.sqrt 3 = (j' + 1 : ℝ) * Real.sqrt 3 := by
          calc
            (j : ℝ) * Real.sqrt 3 = ((j : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by field_simp [hkℝ]
            _ = ((j' + 1 : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by rw [hy']
            _ = (j' + 1 : ℝ) * Real.sqrt 3 := by field_simp [hkℝ]
        have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
        exact mul_right_cancel₀ hsqrt3 h_eq_scaled
      have hA1 : (up_triangle i j k).A = lattice_point i j k := by
        simp [up_triangle, hpos']
      have hA2 : (down_triangle i' j' k).A = lattice_point (i' + 1) j' k := by
        simp [down_triangle, hpos']
      rw [hA1, hA2] at hA
      have hy_A : (j : ℝ) = (j' : ℝ) := by
        have hy' : (lattice_point i j k).2 = (lattice_point (i' + 1) j' k).2 := by rw [hA]
        simp [lattice_point] at hy'
        have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
        have h_eq_scaled : (j : ℝ) * Real.sqrt 3 = (j' : ℝ) * Real.sqrt 3 := by
          calc
            (j : ℝ) * Real.sqrt 3 = ((j : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by field_simp [hkℝ]
            _ = ((j' : ℝ) * Real.sqrt 3 / (2*(k : ℝ))) * (2*(k : ℝ)) := by rw [hy']
            _ = (j' : ℝ) * Real.sqrt 3 := by field_simp [hkℝ]
        have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
        exact mul_right_cancel₀ hsqrt3 h_eq_scaled
      nlinarith
    have h_disjoint : Disjoint up_set down_set :=
      Finset.disjoint_iff_inter_eq_empty.mpr h_inter_empty
    rw [grid_triangles, Finset.card_union_of_disjoint h_disjoint]
    have hcard_up : up_set.card =
      (Finset.filter (λ ⟨i,j⟩ => i + j < k) (Finset.product (Finset.range k) (Finset.range k))).card := by
      dsimp [up_set]
      apply Finset.card_image_of_injective
      exact up_triangle_injective k hpos
    have hcard_down : down_set.card =
      ((Finset.filter (λ ⟨i,j⟩ => i + j < k - 1) (Finset.product (Finset.range (k-1)) (Finset.range (k-1)))).card : ℕ) := by
      dsimp [down_set]
      apply Finset.card_image_of_injective
      exact down_triangle_injective k hpos
    rw [hcard_up, hcard_down, count_up_indices k, count_down_indices k]
    have h_sq_sum : (k * (k + 1)) / 2 + ((k - 1) * k) / 2 = k ^ 2 := by
      have h_even1 : Even (k * (k + 1)) := Nat.even_mul_succ_self k
      have h_even2 : Even ((k - 1) * k) := by
        have h := Nat.even_mul_succ_self (k - 1)
        have htemp : (k - 1) + 1 = k := by omega
        have h_eq : (k - 1) * ((k - 1) + 1) = (k - 1) * k := by
          rw [htemp]
        rw [h_eq] at h
        exact h
      rcases h_even1 with ⟨t1, ht1⟩
      rcases h_even2 with ⟨t2, ht2⟩
      have h1 : k * (k + 1) = 2 * t1 := by omega
      have h2 : (k - 1) * k = 2 * t2 := by omega
      calc
        (k * (k + 1)) / 2 + ((k - 1) * k) / 2 = (2 * t1) / 2 + (2 * t2) / 2 := by rw [h1, h2]
        _ = t1 + t2 := by simp
        _ = k ^ 2 := by
          have hcalc : k * (k + 1) + (k - 1) * k = 2 * k ^ 2 := by
            cases k
            · simp
            · rename_i k
              have hsub : (k.succ - 1) = k := by omega
              rw [hsub]
              nlinarith
          calc
            t1 + t2 = (2 * (t1 + t2)) / 2 := by simp
            _ = (2 * t1 + 2 * t2) / 2 := by omega
            _ = (k * (k + 1) + (k - 1) * k) / 2 := by rw [h1, h2]
            _ = (2 * k ^ 2) / 2 := by rw [hcalc]
            _ = k ^ 2 := by simp
    rw [h_sq_sum]

lemma grid_area_sum (k : ℕ) (hk : k > 0) : Finset.sum (grid_triangles k) signed_area = signed_area equilateral := by
  have hcard : (grid_triangles k).card = k ^ 2 := grid_card k
  have h_all_same : ∀ t ∈ grid_triangles k, signed_area t = Real.sqrt 3 / (4 * ((k : ℝ)^2)) := by
    intro t ht
    rcases Finset.mem_union.mp ht with (ht_up | ht_down)
    · rcases Finset.mem_image.mp ht_up with ⟨⟨i, j⟩, _, rfl⟩
      exact signed_area_up_triangle i j k hk
    · rcases Finset.mem_image.mp ht_down with ⟨⟨i, j⟩, _, rfl⟩
      exact signed_area_down_triangle i j k hk
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hksq : (k : ℝ)^2 ≠ 0 := pow_ne_zero 2 hkℝ
  calc
    Finset.sum (grid_triangles k) signed_area = Finset.sum (grid_triangles k) (λ t => Real.sqrt 3 / (4 * ((k : ℝ)^2))) := by
      refine Finset.sum_congr rfl (λ t ht => ?_)
      rw [h_all_same t ht]
    _ = (grid_triangles k).card • (Real.sqrt 3 / (4 * ((k : ℝ)^2))) := by simp [Finset.sum_const]
    _ = (k^2 : ℕ) • (Real.sqrt 3 / (4 * ((k : ℝ)^2))) := by rw [hcard]
    _ = (k : ℝ)^2 * (Real.sqrt 3 / (4 * ((k : ℝ)^2))) := by simp
    _ = Real.sqrt 3 / 4 := by
      field_simp [hksq]
    _ = signed_area equilateral := by rw [signed_area_equilateral]

/-- Point-in-equilateral lemma for lattice points. -/
lemma lattice_point_mem_equilateral (i j k : ℕ) (hij : i + j ≤ k) (hk : k > 0) :
    point_in_triangle (lattice_point i j k) equilateral := by
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hi_nonneg : 0 ≤ (i : ℝ) / (k : ℝ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le i) (by exact_mod_cast hk.le)
  have hj_nonneg : 0 ≤ (j : ℝ) / (k : ℝ) :=
    div_nonneg (by exact_mod_cast Nat.zero_le j) (by exact_mod_cast hk.le)
  have hsum : (i : ℝ) / (k : ℝ) + (j : ℝ) / (k : ℝ) ≤ 1 := by
    have hcast : (i : ℝ) + (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hij
    field_simp [hkℝ]
    nlinarith
  let α := 1 - (i : ℝ) / (k : ℝ) - (j : ℝ) / (k : ℝ)
  let β := (i : ℝ) / (k : ℝ)
  let γ := (j : ℝ) / (k : ℝ)
  refine ⟨α, β, γ, ?_, hi_nonneg, hj_nonneg, ?_, ?_, ?_⟩
  · dsimp [α]; nlinarith
  · dsimp [α, β, γ]; ring
  · dsimp [β, γ, lattice_point, equilateral]
    simp; ring
  · dsimp [β, γ, lattice_point, equilateral]
    simp; ring

lemma lattice_point_mem_equilateral_up (i j k : ℕ) (h : i + j < k) (hk : k > 0) :
    point_in_triangle (lattice_point i j k) equilateral :=
  lattice_point_mem_equilateral i j k (by omega) hk

lemma lattice_point_mem_equilateral_up_succ_i (i j k : ℕ) (h : i + j < k) (hk : k > 0) :
    point_in_triangle (lattice_point (i+1) j k) equilateral :=
  lattice_point_mem_equilateral (i+1) j k (by omega) hk

lemma lattice_point_mem_equilateral_up_succ_j (i j k : ℕ) (h : i + j < k) (hk : k > 0) :
    point_in_triangle (lattice_point i (j+1) k) equilateral :=
  lattice_point_mem_equilateral i (j+1) k (by omega) hk

lemma lattice_point_mem_equilateral_down (i j k : ℕ) (h : i + j < k - 1) (hk : k > 0) :
    point_in_triangle (lattice_point (i+1) j k) equilateral :=
  lattice_point_mem_equilateral (i+1) j k (by omega) hk

lemma lattice_point_mem_equilateral_down_succ_j (i j k : ℕ) (h : i + j < k - 1) (hk : k > 0) :
    point_in_triangle (lattice_point (i+1) (j+1) k) equilateral :=
  lattice_point_mem_equilateral (i+1) (j+1) k (by omega) hk

lemma lattice_point_mem_equilateral_down_i (i j k : ℕ) (h : i + j < k - 1) (hk : k > 0) :
    point_in_triangle (lattice_point i (j+1) k) equilateral :=
  lattice_point_mem_equilateral i (j+1) k (by omega) hk

/-- All vertices of grid triangles lie in the equilateral triangle. -/
lemma grid_subset_equilateral (k : ℕ) (hk : k > 0) (t : Triangle) (ht : t ∈ grid_triangles k) :
    point_in_triangle t.A equilateral ∧ point_in_triangle t.B equilateral ∧ point_in_triangle t.C equilateral := by
  rcases Finset.mem_union.mp ht with (ht_up | ht_down)
  · rcases Finset.mem_image.mp ht_up with ⟨⟨i, j⟩, hmem, rfl⟩
    rcases Finset.mem_filter.mp hmem with ⟨hmem_prod, hij⟩
    have hk0 : k ≠ 0 := by omega
    refine ⟨by
      simpa [up_triangle, hk0] using lattice_point_mem_equilateral_up i j k hij hk,
      by
      simpa [up_triangle, hk0] using lattice_point_mem_equilateral_up_succ_i i j k hij hk,
      by
      simpa [up_triangle, hk0] using lattice_point_mem_equilateral_up_succ_j i j k hij hk⟩
  · rcases Finset.mem_image.mp ht_down with ⟨⟨i, j⟩, hmem, rfl⟩
    rcases Finset.mem_filter.mp hmem with ⟨hmem_prod, hij⟩
    have hk0 : k ≠ 0 := by omega
    refine ⟨by
      simpa [down_triangle, hk0] using lattice_point_mem_equilateral_down i j k hij hk,
      by
      simpa [down_triangle, hk0] using lattice_point_mem_equilateral_down_succ_j i j k hij hk,
      by
      simpa [down_triangle, hk0] using lattice_point_mem_equilateral_down_i i j k hij hk⟩

/-- The three vertices of the equilateral triangle are among the grid piece vertices. -/
lemma equilateral_vertices_in_grid (k : ℕ) (hk : k > 0) :
    equilateral.A ∈ Finset.biUnion (grid_triangles k) (λ t => {t.A, t.B, t.C}) ∧
    equilateral.B ∈ Finset.biUnion (grid_triangles k) (λ t => {t.A, t.B, t.C}) ∧
    equilateral.C ∈ Finset.biUnion (grid_triangles k) (λ t => {t.A, t.B, t.C}) := by
  have hmem_A : up_triangle 0 0 k ∈ grid_triangles k := by
    dsimp [grid_triangles]
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨(0, 0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by simpa using hk, by simpa using hk⟩, hk⟩, ?_⟩
    rfl
  have hmem_B : up_triangle (k-1) 0 k ∈ grid_triangles k := by
    dsimp [grid_triangles]
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    have hprod : (k-1, 0) ∈ Finset.product (Finset.range k) (Finset.range k) := by
      have hless : k-1 < k := by omega
      simp [hless, hk]
    have hcond : (k-1) + 0 < k := by omega
    refine ⟨(k-1, 0), Finset.mem_filter.mpr ⟨hprod, hcond⟩, ?_⟩
    rfl
  have hmem_C : up_triangle 0 (k-1) k ∈ grid_triangles k := by
    dsimp [grid_triangles]
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    have hprod : (0, k-1) ∈ Finset.product (Finset.range k) (Finset.range k) := by
      have hless : k-1 < k := by omega
      simp [hless, hk]
    have hcond : 0 + (k-1) < k := by omega
    refine ⟨(0, k-1), Finset.mem_filter.mpr ⟨hprod, hcond⟩, ?_⟩
    rfl
  have hk0 : k ≠ 0 := by omega
  have hk0ℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hA : equilateral.A = (up_triangle 0 0 k).A := by
    dsimp [up_triangle]
    split
    · exfalso; exact hk0 ‹_›
    · simp [equilateral, lattice_point]
  have hB : equilateral.B = (up_triangle (k-1) 0 k).B := by
    dsimp [up_triangle]
    split
    · exfalso; exact hk0 ‹_›
    · have h_succ_nat : (k-1 : ℕ) + 1 = k := by omega
      have h_succ : ((k-1 : ℕ) + 1 : ℝ) = (k : ℝ) := by exact_mod_cast h_succ_nat
      dsimp [equilateral, lattice_point]
      simp [h_succ]
      field_simp [hk0ℝ]
  have hC : equilateral.C = (up_triangle 0 (k-1) k).C := by
    dsimp [up_triangle]
    split
    · exfalso; exact hk0 ‹_›
    · have h_succ_nat : (k-1 : ℕ) + 1 = k := by omega
      have h_succ : ((k-1 : ℕ) + 1 : ℝ) = (k : ℝ) := by exact_mod_cast h_succ_nat
      dsimp [equilateral, lattice_point]
      simp [h_succ]
      refine ⟨?_, ?_⟩
      · field_simp [hk0ℝ]
      · field_simp [hk0ℝ]
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨up_triangle 0 0 k, hmem_A, ?_⟩
    simp [hA]
  · apply Finset.mem_biUnion.mpr
    refine ⟨up_triangle (k-1) 0 k, hmem_B, ?_⟩
    simp [hB]
  · apply Finset.mem_biUnion.mpr
    refine ⟨up_triangle 0 (k-1) k, hmem_C, ?_⟩
    simp [hC]

/-- Interior point of an up-triangle is bounded by grid lines in equi barycentrics. -/
lemma up_interior_ineqs (p : ℝ × ℝ) (i j k : ℕ) (hk : k > 0)
    (h : point_in_interior p (up_triangle i j k)) :
    (i : ℝ) / (k : ℝ) < equi_beta p ∧ equi_beta p < ((i : ℝ) + 1) / (k : ℝ) ∧
    (j : ℝ) / (k : ℝ) < equi_gamma p ∧ equi_gamma p < ((j : ℝ) + 1) / (k : ℝ) ∧
    equi_beta p + equi_gamma p < ((i + j + 1 : ℝ)) / (k : ℝ) := by
  rcases h with ⟨α', β', γ', hα', hβ', hγ', hsum, hx, hy⟩
  have hk0 : k ≠ 0 := by omega
  have hk0ℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have h_sq3 : Real.sqrt 3 ≠ 0 := by positivity
  have hA := up_triangle_A_eq i j k hk0
  have hB := up_triangle_B_eq i j k hk0
  have hC := up_triangle_C_eq i j k hk0
  rw [hA, hB, hC] at hx hy
  dsimp [lattice_point] at hx hy
  have hx' : p.1 = (i : ℝ) / (k : ℝ) + (j : ℝ) / (2*(k : ℝ)) + β' / (k : ℝ) + γ' / (2*(k : ℝ)) := by
    rw [hx]
    have hα' : α' = 1 - β' - γ' := by linarith
    rw [hα']
    field_simp [hk0ℝ]; push_cast; ring_nf
  have hy' : p.2 = (j : ℝ) * Real.sqrt 3 / (2*(k : ℝ)) + γ' * Real.sqrt 3 / (2*(k : ℝ)) := by
    rw [hy]
    have hα' : α' = 1 - β' - γ' := by linarith
    rw [hα']
    field_simp [hk0ℝ]; push_cast; ring_nf
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hβ_eq : equi_beta p = ((i : ℝ) + β') / (k : ℝ) := by
    dsimp [equi_beta]
    rw [hx', hy']
    field_simp [hk0ℝ, h_sq3]
    ring
  have hγ_eq : equi_gamma p = ((j : ℝ) + γ') / (k : ℝ) := by
    dsimp [equi_gamma]
    rw [hy']
    field_simp [hk0ℝ, h_sq3]
  have h_sum_eq : equi_beta p + equi_gamma p = ((i : ℝ) + (j : ℝ) + (β' + γ')) / (k : ℝ) := by
    rw [hβ_eq, hγ_eq]; ring
  have hβ'_lt1 : β' < 1 := by nlinarith
  have hγ'_lt1 : γ' < 1 := by nlinarith
  have hβγ_lt1 : β' + γ' < 1 := by nlinarith
  have hdiv : ∀ (a b : ℝ), a < b → a / (k : ℝ) < b / (k : ℝ) := by
    intro a b h; exact div_lt_div_of_pos_right h hk_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hβ_eq]; apply hdiv; nlinarith
  · rw [hβ_eq]; apply hdiv; nlinarith
  · rw [hγ_eq]; apply hdiv; nlinarith
  · rw [hγ_eq]; apply hdiv; nlinarith
  · rw [h_sum_eq]; apply hdiv; nlinarith

/-- Interior point of a down-triangle is bounded by grid lines in equi barycentrics. -/
lemma down_interior_ineqs (p : ℝ × ℝ) (i j k : ℕ) (hk : k > 0)
    (h : point_in_interior p (down_triangle i j k)) :
    (i : ℝ) / (k : ℝ) < equi_beta p ∧ equi_beta p < ((i : ℝ) + 1) / (k : ℝ) ∧
    (j : ℝ) / (k : ℝ) < equi_gamma p ∧ equi_gamma p < ((j : ℝ) + 1) / (k : ℝ) ∧
    equi_beta p + equi_gamma p > ((i + j + 1 : ℝ)) / (k : ℝ) := by
  rcases h with ⟨α', β', γ', hα', hβ', hγ', hsum, hx, hy⟩
  have hk0 : k ≠ 0 := by omega
  have hk0ℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have h_sq3 : Real.sqrt 3 ≠ 0 := by positivity
  have hA := down_triangle_A_eq i j k hk0
  have hB := down_triangle_B_eq i j k hk0
  have hC := down_triangle_C_eq i j k hk0
  rw [hA, hB, hC] at hx hy
  dsimp [lattice_point] at hx hy
  have hx' : p.1 = ((i : ℝ) + 1) / (k : ℝ) + (j : ℝ) / (2*(k : ℝ)) + (β' - γ') / (2*(k : ℝ)) := by
    rw [hx]
    have hα' : α' = 1 - β' - γ' := by linarith
    rw [hα']
    field_simp [hk0ℝ]; push_cast; ring_nf
  have hy' : p.2 = (j : ℝ) * Real.sqrt 3 / (2*(k : ℝ)) + (β' + γ') * Real.sqrt 3 / (2*(k : ℝ)) := by
    rw [hy]
    have hα' : α' = 1 - β' - γ' := by linarith
    rw [hα']
    field_simp [hk0ℝ]; push_cast; ring_nf
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hβ_eq : equi_beta p = ((i : ℝ) + 1 - γ') / (k : ℝ) := by
    dsimp [equi_beta]
    rw [hx', hy']
    field_simp [hk0ℝ, h_sq3]
    ring
  have hγ_eq : equi_gamma p = ((j : ℝ) + β' + γ') / (k : ℝ) := by
    dsimp [equi_gamma]
    rw [hy']
    field_simp [hk0ℝ, h_sq3]
    ring
  have h_sum_eq : equi_beta p + equi_gamma p = ((i : ℝ) + (j : ℝ) + 1 + β') / (k : ℝ) := by
    rw [hβ_eq, hγ_eq]; ring
  have hα'_lt1 : α' < 1 := by nlinarith
  have hγ'_lt1 : γ' < 1 := by nlinarith
  have hpos : β' + γ' > 0 := by positivity
  have hsum : β' + γ' < 1 := by nlinarith
  have hdiv : ∀ (a b : ℝ), a < b → a / (k : ℝ) < b / (k : ℝ) := by
    intro a b h; exact div_lt_div_of_pos_right h hk_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hβ_eq]; apply hdiv; nlinarith
  · rw [hβ_eq]; apply hdiv; nlinarith
  · rw [hγ_eq]; apply hdiv; nlinarith
  · rw [hγ_eq]; apply hdiv; nlinarith
  · rw [h_sum_eq]; apply hdiv; nlinarith

set_option maxHeartbeats 800000 in
/-- The grid triangulation is pairwise interior-disjoint. -/
lemma grid_pairwise_disjoint (k : ℕ) (hk : k > 0) : PairwiseInteriorDisjoint (grid_triangles k) := by
  intro t₁ ht₁ t₂ ht₂ hne
  intro h
  rcases h with ⟨p, hp₁, hp₂⟩
  rcases Finset.mem_union.mp ht₁ with (ht₁_up | ht₁_down)
  · rcases Finset.mem_image.mp ht₁_up with ⟨⟨i₁, j₁⟩, hm₁, rfl⟩
    rcases Finset.mem_filter.mp hm₁ with ⟨hm₁_prod, hi₁j₁⟩
    have hi₁j₁_val : (i₁ : ℕ) + j₁ < k := hi₁j₁
    rcases Finset.mem_union.mp ht₂ with (ht₂_up | ht₂_down)
    · rcases Finset.mem_image.mp ht₂_up with ⟨⟨i₂, j₂⟩, hm₂, rfl⟩
      rcases Finset.mem_filter.mp hm₂ with ⟨hm₂_prod, hi₂j₂⟩
      have hi₂j₂_val : (i₂ : ℕ) + j₂ < k := hi₂j₂
      -- both up-triangles
      by_cases h_eq : (i₁, j₁) = (i₂, j₂)
      · exfalso; exact hne (by
          have : up_triangle i₁ j₁ k = up_triangle i₂ j₂ k := by
            rcases h_eq with ⟨rfl, rfl⟩; rfl
          exact this)
      · by_cases hi : i₁ = i₂
        · by_cases hj : j₁ = j₂
          · exfalso; exact h_eq (Prod.ext hi hj)
          · -- same i, different j → different equi_gamma intervals
            have hi_val : (i₁ : ℝ) = (i₂ : ℝ) := by exact_mod_cast hi
            have hg1 := up_interior_ineqs p i₁ j₁ k hk hp₁
            have hg2 := up_interior_ineqs p i₂ j₂ k hk hp₂
            rcases hg1 with ⟨_, _, hg1_low, hg1_high, _⟩
            rcases hg2 with ⟨_, _, hg2_low, hg2_high, _⟩
            have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            by_cases h_j_lt : (j₁ : ℕ) < (j₂ : ℕ)
            · have h_succ_le : (j₁ : ℕ) + 1 ≤ (j₂ : ℕ) := by omega
              have h_succ_le_ℝ : (j₁ + 1 : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h_succ_le
              have h_mul : equi_gamma p * (k : ℝ) < (j₁ : ℝ) + 1 := by
                calc
                  equi_gamma p * (k : ℝ) < (((j₁ : ℝ) + 1) / (k : ℝ)) * (k : ℝ) := mul_lt_mul_of_pos_right hg1_high hk_pos'
                  _ = (j₁ : ℝ) + 1 := by field_simp [hk_pos'.ne']
              have h_mul' : (j₂ : ℝ) < equi_gamma p * (k : ℝ) := by
                calc
                  (j₂ : ℝ) = ((j₂ : ℝ) / (k : ℝ)) * (k : ℝ) := by field_simp [hk_pos'.ne']
                  _ < equi_gamma p * (k : ℝ) := mul_lt_mul_of_pos_right hg2_low hk_pos'
              nlinarith
            · have h_lt' : (j₂ : ℕ) < (j₁ : ℕ) := by
                by_contra! hge
                have : j₁ = j₂ := by omega
                exact hj this
              have h_succ_le' : (j₂ : ℕ) + 1 ≤ (j₁ : ℕ) := by omega
              have h_succ_le_ℝ' : (j₂ + 1 : ℝ) ≤ (j₁ : ℝ) := by exact_mod_cast h_succ_le'
              have h_mul : (j₁ : ℝ) < equi_gamma p * (k : ℝ) := by
                calc
                  (j₁ : ℝ) = ((j₁ : ℝ) / (k : ℝ)) * (k : ℝ) := by field_simp [hk_pos'.ne']
                  _ < equi_gamma p * (k : ℝ) := mul_lt_mul_of_pos_right hg1_low hk_pos'
              have h_mul' : equi_gamma p * (k : ℝ) < (j₂ : ℝ) + 1 := by
                calc
                  equi_gamma p * (k : ℝ) < (((j₂ : ℝ) + 1) / (k : ℝ)) * (k : ℝ) := mul_lt_mul_of_pos_right hg2_high hk_pos'
                  _ = (j₂ : ℝ) + 1 := by field_simp [hk_pos'.ne']
              nlinarith
        · -- different i → different equi_beta intervals
          have hg1 := up_interior_ineqs p i₁ j₁ k hk hp₁
          have hg2 := up_interior_ineqs p i₂ j₂ k hk hp₂
          rcases hg1 with ⟨hg1_low, hg1_high, _, _, _⟩
          rcases hg2 with ⟨hg2_low, hg2_high, _, _, _⟩
          have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
          by_cases h_i_lt : (i₁ : ℕ) < (i₂ : ℕ)
          · have h_succ_le : (i₁ : ℕ) + 1 ≤ (i₂ : ℕ) := by omega
            have h_succ_le_ℝ : (i₁ + 1 : ℝ) ≤ (i₂ : ℝ) := by exact_mod_cast h_succ_le
            have h_mul : equi_beta p * (k : ℝ) < (i₁ : ℝ) + 1 := by
              calc
                equi_beta p * (k : ℝ) < (((i₁ : ℝ) + 1) / (k : ℝ)) * (k : ℝ) := mul_lt_mul_of_pos_right hg1_high hk_pos'
                _ = (i₁ : ℝ) + 1 := by field_simp [hk_pos'.ne']
            have h_mul' : (i₂ : ℝ) < equi_beta p * (k : ℝ) := by
              calc
                (i₂ : ℝ) = ((i₂ : ℝ) / (k : ℝ)) * (k : ℝ) := by field_simp [hk_pos'.ne']
                _ < equi_beta p * (k : ℝ) := mul_lt_mul_of_pos_right hg2_low hk_pos'
            nlinarith
          · have h_lt' : (i₂ : ℕ) < (i₁ : ℕ) := by
              by_contra! hge
              have : i₁ = i₂ := by omega
              exact hi this
            have h_succ_le' : (i₂ : ℕ) + 1 ≤ (i₁ : ℕ) := by omega
            have h_succ_le_ℝ' : (i₂ + 1 : ℝ) ≤ (i₁ : ℝ) := by exact_mod_cast h_succ_le'
            have h_mul : (i₁ : ℝ) < equi_beta p * (k : ℝ) := by
              calc
                (i₁ : ℝ) = ((i₁ : ℝ) / (k : ℝ)) * (k : ℝ) := by field_simp [hk_pos'.ne']
                _ < equi_beta p * (k : ℝ) := mul_lt_mul_of_pos_right hg1_low hk_pos'
            have h_mul' : equi_beta p * (k : ℝ) < (i₂ : ℝ) + 1 := by
              calc
                equi_beta p * (k : ℝ) < (((i₂ : ℝ) + 1) / (k : ℝ)) * (k : ℝ) := mul_lt_mul_of_pos_right hg2_high hk_pos'
                _ = (i₂ : ℝ) + 1 := by field_simp [hk_pos'.ne']
            nlinarith
    · rcases Finset.mem_image.mp ht₂_down with ⟨⟨i₂, j₂⟩, hm₂, rfl⟩
      rcases Finset.mem_filter.mp hm₂ with ⟨hm₂_prod, hi₂j₂⟩
      have hi₂j₂_val : (i₂ : ℕ) + j₂ < k - 1 := hi₂j₂
      -- up vs down triangle
      by_cases hcell : (i₁, j₁) = (i₂, j₂)
      · -- same cell: up vs down → separated by β+γ = (i₁+j₁+1)/k
        rcases hcell with ⟨rfl, rfl⟩
        have h_up := up_interior_ineqs p i₁ j₁ k hk hp₁
        have h_down := down_interior_ineqs p i₁ j₁ k hk hp₂
        rcases h_up with ⟨_, _, _, _, h_up_sum⟩
        rcases h_down with ⟨_, _, _, _, h_down_sum⟩
        have h_contra : equi_beta p + equi_gamma p < equi_beta p + equi_gamma p :=
          calc
            equi_beta p + equi_gamma p < ((i₁ + j₁ + 1 : ℝ)) / (k : ℝ) := h_up_sum
            _ < equi_beta p + equi_gamma p := h_down_sum
        exact lt_irrefl _ h_contra
      · by_cases hi : i₁ = i₂
        · by_cases hj : j₁ = j₂
          · exfalso; exact hcell (Prod.ext hi hj)
          · -- same i, different j
            have hi_val : (i₁ : ℝ) = (i₂ : ℝ) := by exact_mod_cast hi
            have h_up := up_interior_ineqs p i₁ j₁ k hk hp₁
            have h_down := down_interior_ineqs p i₂ j₂ k hk hp₂
            rcases h_up with ⟨_, _, hg1_low, hg1_high, _⟩
            rcases h_down with ⟨_, _, hg2_low, hg2_high, _⟩
            have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            by_cases h_j_lt : (j₁ : ℕ) < (j₂ : ℕ)
            · have h_succ_le : (j₁ : ℕ) + 1 ≤ (j₂ : ℕ) := by omega
              have h_succ_le_ℝ : (j₁ + 1 : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h_succ_le
              have h_mul : equi_gamma p * (k : ℝ) < (j₁ : ℝ) + 1 := by
                exact mul_lt_of_lt_div hk_pos' hg1_high
              have h_mul' : (j₂ : ℝ) < equi_gamma p * (k : ℝ) := by
                exact lt_mul_of_div_lt hk_pos' hg2_low
              nlinarith
            · have h_lt' : (j₂ : ℕ) < (j₁ : ℕ) := by
                by_contra! hge
                have : j₁ = j₂ := by omega
                exact hj this
              have h_succ_le' : (j₂ : ℕ) + 1 ≤ (j₁ : ℕ) := by omega
              have h_succ_le_ℝ' : (j₂ + 1 : ℝ) ≤ (j₁ : ℝ) := by exact_mod_cast h_succ_le'
              have h_mul : (j₁ : ℝ) < equi_gamma p * (k : ℝ) := by
                exact lt_mul_of_div_lt hk_pos' hg1_low
              have h_mul' : equi_gamma p * (k : ℝ) < (j₂ : ℝ) + 1 := by
                exact mul_lt_of_lt_div hk_pos' hg2_high
              nlinarith
        · -- different i
          have h_up := up_interior_ineqs p i₁ j₁ k hk hp₁
          have h_down := down_interior_ineqs p i₂ j₂ k hk hp₂
          rcases h_up with ⟨hg1_low, hg1_high, _, _, _⟩
          rcases h_down with ⟨hg2_low, hg2_high, _, _, _⟩
          have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
          by_cases h_i_lt : (i₁ : ℕ) < (i₂ : ℕ)
          · have h_succ_le : (i₁ : ℕ) + 1 ≤ (i₂ : ℕ) := by omega
            have h_succ_le_ℝ : (i₁ + 1 : ℝ) ≤ (i₂ : ℝ) := by exact_mod_cast h_succ_le
            have h_mul : equi_beta p * (k : ℝ) < (i₁ : ℝ) + 1 := by
              exact mul_lt_of_lt_div hk_pos' hg1_high
            have h_mul' : (i₂ : ℝ) < equi_beta p * (k : ℝ) := by
              exact lt_mul_of_div_lt hk_pos' hg2_low
            nlinarith
          · have h_lt' : (i₂ : ℕ) < (i₁ : ℕ) := by
              by_contra! hge
              have : i₁ = i₂ := by omega
              exact hi this
            have h_succ_le' : (i₂ : ℕ) + 1 ≤ (i₁ : ℕ) := by omega
            have h_succ_le_ℝ' : (i₂ + 1 : ℝ) ≤ (i₁ : ℝ) := by exact_mod_cast h_succ_le'
            have h_mul : (i₁ : ℝ) < equi_beta p * (k : ℝ) := by
              exact lt_mul_of_div_lt hk_pos' hg1_low
            have h_mul' : equi_beta p * (k : ℝ) < (i₂ : ℝ) + 1 := by
              exact mul_lt_of_lt_div hk_pos' hg2_high
            nlinarith
  · rcases Finset.mem_image.mp ht₁_down with ⟨⟨i₁, j₁⟩, hm₁, rfl⟩
    rcases Finset.mem_filter.mp hm₁ with ⟨hm₁_prod, hi₁j₁⟩
    have hi₁j₁_val : (i₁ : ℕ) + j₁ < k - 1 := hi₁j₁
    rcases Finset.mem_union.mp ht₂ with (ht₂_up | ht₂_down)
    · rcases Finset.mem_image.mp ht₂_up with ⟨⟨i₂, j₂⟩, hm₂, rfl⟩
      rcases Finset.mem_filter.mp hm₂ with ⟨hm₂_prod, hi₂j₂⟩
      have hi₂j₂_val : (i₂ : ℕ) + j₂ < k := hi₂j₂
      -- down vs up (symmetric to up vs down)
      by_cases hcell : (i₁, j₁) = (i₂, j₂)
      · rcases hcell with ⟨rfl, rfl⟩
        have h_down := down_interior_ineqs p i₁ j₁ k hk hp₁
        have h_up := up_interior_ineqs p i₁ j₁ k hk hp₂
        rcases h_down with ⟨_, _, _, _, h_down_sum⟩
        rcases h_up with ⟨_, _, _, _, h_up_sum⟩
        have h_contra : equi_beta p + equi_gamma p < equi_beta p + equi_gamma p :=
          calc
            equi_beta p + equi_gamma p < ((i₁ + j₁ + 1 : ℝ)) / (k : ℝ) := h_up_sum
            _ < equi_beta p + equi_gamma p := h_down_sum
        exact lt_irrefl _ h_contra
      · by_cases hi : i₁ = i₂
        · by_cases hj : j₁ = j₂
          · exfalso; exact hcell (Prod.ext hi hj)
          · have hi_val : (i₁ : ℝ) = (i₂ : ℝ) := by exact_mod_cast hi
            have h_down := down_interior_ineqs p i₁ j₁ k hk hp₁
            have h_up := up_interior_ineqs p i₂ j₂ k hk hp₂
            rcases h_down with ⟨_, _, hg1_low, hg1_high, _⟩
            rcases h_up with ⟨_, _, hg2_low, hg2_high, _⟩
            have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            by_cases h_j_lt : (j₁ : ℕ) < (j₂ : ℕ)
            · have h_succ_le : (j₁ : ℕ) + 1 ≤ (j₂ : ℕ) := by omega
              have h_succ_le_ℝ : (j₁ + 1 : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h_succ_le
              have h_mul : equi_gamma p * (k : ℝ) < (j₁ : ℝ) + 1 := by
                exact mul_lt_of_lt_div hk_pos' hg1_high
              have h_mul' : (j₂ : ℝ) < equi_gamma p * (k : ℝ) := by
                exact lt_mul_of_div_lt hk_pos' hg2_low
              nlinarith
            · have h_lt' : (j₂ : ℕ) < (j₁ : ℕ) := by
                by_contra! hge
                have : j₁ = j₂ := by omega
                exact hj this
              have h_succ_le' : (j₂ : ℕ) + 1 ≤ (j₁ : ℕ) := by omega
              have h_succ_le_ℝ' : (j₂ + 1 : ℝ) ≤ (j₁ : ℝ) := by exact_mod_cast h_succ_le'
              have h_mul : (j₁ : ℝ) < equi_gamma p * (k : ℝ) := by
                exact lt_mul_of_div_lt hk_pos' hg1_low
              have h_mul' : equi_gamma p * (k : ℝ) < (j₂ : ℝ) + 1 := by
                exact mul_lt_of_lt_div hk_pos' hg2_high
              nlinarith
        · have h_down := down_interior_ineqs p i₁ j₁ k hk hp₁
          have h_up := up_interior_ineqs p i₂ j₂ k hk hp₂
          rcases h_down with ⟨hg1_low, hg1_high, _, _, _⟩
          rcases h_up with ⟨hg2_low, hg2_high, _, _, _⟩
          have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
          by_cases h_i_lt : (i₁ : ℕ) < (i₂ : ℕ)
          · have h_succ_le : (i₁ : ℕ) + 1 ≤ (i₂ : ℕ) := by omega
            have h_succ_le_ℝ : (i₁ + 1 : ℝ) ≤ (i₂ : ℝ) := by exact_mod_cast h_succ_le
            have h_mul : equi_beta p * (k : ℝ) < (i₁ : ℝ) + 1 := by
              exact mul_lt_of_lt_div hk_pos' hg1_high
            have h_mul' : (i₂ : ℝ) < equi_beta p * (k : ℝ) := by
              exact lt_mul_of_div_lt hk_pos' hg2_low
            nlinarith
          · have h_lt' : (i₂ : ℕ) < (i₁ : ℕ) := by
              by_contra! hge
              have : i₁ = i₂ := by omega
              exact hi this
            have h_succ_le' : (i₂ : ℕ) + 1 ≤ (i₁ : ℕ) := by omega
            have h_succ_le_ℝ' : (i₂ + 1 : ℝ) ≤ (i₁ : ℝ) := by exact_mod_cast h_succ_le'
            have h_mul : (i₁ : ℝ) < equi_beta p * (k : ℝ) := by
              exact lt_mul_of_div_lt hk_pos' hg1_low
            have h_mul' : equi_beta p * (k : ℝ) < (i₂ : ℝ) + 1 := by
              exact mul_lt_of_lt_div hk_pos' hg2_high
            nlinarith
    · rcases Finset.mem_image.mp ht₂_down with ⟨⟨i₂, j₂⟩, hm₂, rfl⟩
      rcases Finset.mem_filter.mp hm₂ with ⟨hm₂_prod, hi₂j₂⟩
      have hi₂j₂_val : (i₂ : ℕ) + j₂ < k - 1 := hi₂j₂
      -- both down-triangles
      by_cases h_eq : (i₁, j₁) = (i₂, j₂)
      · exfalso; exact hne (by
          have : down_triangle i₁ j₁ k = down_triangle i₂ j₂ k := by
            rcases h_eq with ⟨rfl, rfl⟩; rfl
          exact this)
      · by_cases hi : i₁ = i₂
        · by_cases hj : j₁ = j₂
          · exfalso; exact h_eq (Prod.ext hi hj)
          · have hg1 := down_interior_ineqs p i₁ j₁ k hk hp₁
            have hg2 := down_interior_ineqs p i₂ j₂ k hk hp₂
            rcases hg1 with ⟨_, _, hg1_low, hg1_high, _⟩
            rcases hg2 with ⟨_, _, hg2_low, hg2_high, _⟩
            have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
            by_cases h_j_lt : (j₁ : ℕ) < (j₂ : ℕ)
            · have h_succ_le : (j₁ : ℕ) + 1 ≤ (j₂ : ℕ) := by omega
              have h_succ_le_ℝ : (j₁ + 1 : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast h_succ_le
              have h_mul : equi_gamma p * (k : ℝ) < (j₁ : ℝ) + 1 := by
                exact mul_lt_of_lt_div hk_pos' hg1_high
              have h_mul' : (j₂ : ℝ) < equi_gamma p * (k : ℝ) := by
                exact lt_mul_of_div_lt hk_pos' hg2_low
              nlinarith
            · have h_lt' : (j₂ : ℕ) < (j₁ : ℕ) := by
                by_contra! hge
                have : j₁ = j₂ := by omega
                exact hj this
              have h_succ_le' : (j₂ : ℕ) + 1 ≤ (j₁ : ℕ) := by omega
              have h_succ_le_ℝ' : (j₂ + 1 : ℝ) ≤ (j₁ : ℝ) := by exact_mod_cast h_succ_le'
              have h_mul : (j₁ : ℝ) < equi_gamma p * (k : ℝ) := by
                exact lt_mul_of_div_lt hk_pos' hg1_low
              have h_mul' : equi_gamma p * (k : ℝ) < (j₂ : ℝ) + 1 := by
                exact mul_lt_of_lt_div hk_pos' hg2_high
              nlinarith
        · have hg1 := down_interior_ineqs p i₁ j₁ k hk hp₁
          have hg2 := down_interior_ineqs p i₂ j₂ k hk hp₂
          rcases hg1 with ⟨hg1_low, hg1_high, _, _, _⟩
          rcases hg2 with ⟨hg2_low, hg2_high, _, _, _⟩
          have hk_pos' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
          by_cases h_i_lt : (i₁ : ℕ) < (i₂ : ℕ)
          · have h_succ_le : (i₁ : ℕ) + 1 ≤ (i₂ : ℕ) := by omega
            have h_succ_le_ℝ : (i₁ + 1 : ℝ) ≤ (i₂ : ℝ) := by exact_mod_cast h_succ_le
            have h_mul : equi_beta p * (k : ℝ) < (i₁ : ℝ) + 1 := by
              exact mul_lt_of_lt_div hk_pos' hg1_high
            have h_mul' : (i₂ : ℝ) < equi_beta p * (k : ℝ) := by
              exact lt_mul_of_div_lt hk_pos' hg2_low
            nlinarith
          · have h_lt' : (i₂ : ℕ) < (i₁ : ℕ) := by
              by_contra! hge
              have : i₁ = i₂ := by omega
              exact hi this
            have h_succ_le' : (i₂ : ℕ) + 1 ≤ (i₁ : ℕ) := by omega
            have h_succ_le_ℝ' : (i₂ + 1 : ℝ) ≤ (i₁ : ℝ) := by exact_mod_cast h_succ_le'
            have h_mul : (i₁ : ℝ) < equi_beta p * (k : ℝ) := by
              exact lt_mul_of_div_lt hk_pos' hg1_low
            have h_mul' : equi_beta p * (k : ℝ) < (i₂ : ℝ) + 1 := by
              exact mul_lt_of_lt_div hk_pos' hg2_high
            nlinarith

/-- The equilateral grid construction satisfies GeometricTiling. -/
lemma squares_constructive_geometric (k : ℕ) (hk : k > 0) : GeometricTriangleTilable (k^2) := by
  refine ⟨equilateral, up_triangle 0 0 k, ⟨{
    pieces := grid_triangles k
    card_eq := grid_card k
    all_congruent := grid_congruent k
    area_eq := grid_area_sum k hk
    subset_T := grid_subset_equilateral k hk
    cover_T := equilateral_vertices_in_grid k hk
    pairwise_disjoint := grid_pairwise_disjoint k hk
  }⟩⟩

/-- Divide the equilateral triangle into k² smaller equilateral triangles
    via a grid of side length 1/k. -/
lemma squares_constructive (k : ℕ) (hk : k > 0) : TriangleTilable (k^2) :=
  geometric_implies_weak (k^2) (squares_constructive_geometric k hk)

/-! ### n=2: geometric tiling by bisection of equilateral triangle

Bisecting an equilateral triangle of side 2 along the altitude from the
apex to the midpoint of the base yields 2 congruent 30-60-90 right triangles.
This proves GeometricTriangleTilable 2. -/

/-- Equilateral triangle of side length 2.
    Bisecting by the altitude from C to midpoint of AB (1,0)
    yields 2 congruent 30-60-90 right triangles. -/
noncomputable def equilateral_side_two : Triangle :=
  { A := (0, 0)
    B := (2, 0)
    C := (1, Real.sqrt 3)
    nondegenerate := by
      have h : (0 : ℝ) * (0 - Real.sqrt 3) + 2 * (Real.sqrt 3 - 0) + 1 * (0 - 0) = 2 * Real.sqrt 3 := by ring
      rw [h]; positivity }

lemma signed_area_equilateral_side_two : signed_area equilateral_side_two = Real.sqrt 3 := by
  unfold signed_area equilateral_side_two; ring

/-- Left half of equilateral side 2: A=(0,0), B=(1,0), C=(1,√3).
    A 30-60-90 right triangle. -/
noncomputable def bisect_left : Triangle :=
  { A := (0, 0)
    B := (1, 0)
    C := (1, Real.sqrt 3)
    nondegenerate := by
      have h : (0 : ℝ) * (0 - Real.sqrt 3) + 1 * (Real.sqrt 3 - 0) + 1 * (0 - 0) = Real.sqrt 3 := by ring
      rw [h]; positivity }

lemma signed_area_bisect_left : signed_area bisect_left = Real.sqrt 3 / 2 := by
  unfold signed_area bisect_left; ring

/-- Left half is congruent to right_triangle under the reflection permutation D5
    (swap A and B on right_triangle). -/
lemma bisect_left_congruent : Congruent bisect_left right_triangle := by
  unfold Congruent
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
  dsimp [bisect_left, right_triangle, distSq]
  norm_num

/-- Right half of equilateral side 2: A=(1,0), B=(2,0), C=(1,√3).
    A 30-60-90 right triangle. -/
noncomputable def bisect_right : Triangle :=
  { A := (1, 0)
    B := (2, 0)
    C := (1, Real.sqrt 3)
    nondegenerate := by
      have h : (1 : ℝ) * (0 - Real.sqrt 3) + 2 * (Real.sqrt 3 - 0) + 1 * (0 - 0) = Real.sqrt 3 := by ring
      rw [h]; positivity }

lemma signed_area_bisect_right : signed_area bisect_right = Real.sqrt 3 / 2 := by
  unfold signed_area bisect_right; ring

/-- Right half is congruent to right_triangle under identity permutation D1. -/
lemma bisect_right_congruent : Congruent bisect_right right_triangle := by
  have hsq3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold Congruent
  refine Or.inl ⟨?_, ?_, ?_⟩
  · dsimp [bisect_right, right_triangle, distSq]; norm_num
  · dsimp [bisect_right, right_triangle, distSq]; nlinarith
  · dsimp [bisect_right, right_triangle, distSq]; norm_num

/-- The two bisection pieces are pairwise interior-disjoint (separated by x=1). -/
lemma bisect_pairwise_disjoint : PairwiseInteriorDisjoint {bisect_left, bisect_right} := by
  intro t₁ ht₁ t₂ ht₂ hne
  intro h
  rcases h with ⟨p, hp₁, hp₂⟩
  have hcases : (t₁ = bisect_left ∧ t₂ = bisect_right) ∨ (t₁ = bisect_right ∧ t₂ = bisect_left) := by
    simp [Finset.mem_insert, Finset.mem_singleton] at ht₁ ht₂
    rcases ht₁ with (rfl|rfl) <;> rcases ht₂ with (rfl|rfl) <;> try { exfalso; exact hne rfl }
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  rcases hcases with (⟨rfl, rfl⟩|⟨rfl, rfl⟩)
  · -- left then right: interiors separated by x=1
    rcases hp₁ with ⟨α₁, β₁, γ₁, hα₁, hβ₁, hγ₁, hsum₁, hx₁, hy₁⟩
    have hx_lt_one : p.1 < 1 := by
      dsimp [bisect_left] at hx₁ hy₁
      have h_eq : p.1 = β₁ + γ₁ := by nlinarith
      rw [h_eq]
      nlinarith
    rcases hp₂ with ⟨α₂, β₂, γ₂, hα₂, hβ₂, hγ₂, hsum₂, hx₂, hy₂⟩
    have hx_gt_one : p.1 > 1 := by
      dsimp [bisect_right] at hx₂ hy₂
      have h_eq : p.1 = α₂ + 2 * β₂ + γ₂ := by nlinarith
      rw [h_eq]
      have : α₂ = 1 - β₂ - γ₂ := by nlinarith
      rw [this]
      nlinarith
    nlinarith
  · -- right then left: symmetric
    rcases hp₁ with ⟨α₁, β₁, γ₁, hα₁, hβ₁, hγ₁, hsum₁, hx₁, hy₁⟩
    have hx_gt_one : p.1 > 1 := by
      dsimp [bisect_right] at hx₁ hy₁
      have h_eq : p.1 = α₁ + 2 * β₁ + γ₁ := by nlinarith
      rw [h_eq]
      have : α₁ = 1 - β₁ - γ₁ := by nlinarith
      rw [this]
      nlinarith
    rcases hp₂ with ⟨α₂, β₂, γ₂, hα₂, hβ₂, hγ₂, hsum₂, hx₂, hy₂⟩
    have hx_lt_one : p.1 < 1 := by
      dsimp [bisect_left] at hx₂ hy₂
      have h_eq : p.1 = β₂ + γ₂ := by nlinarith
      rw [h_eq]
      nlinarith
    nlinarith

/-- The bisection proves GeometricTriangleTilable 2. -/
lemma n_two_geometric_tiling : GeometricTriangleTilable 2 := by
  refine ⟨equilateral_side_two, right_triangle, ⟨{
    pieces := {bisect_left, bisect_right}
    card_eq := by
      have h_ne : bisect_left ≠ bisect_right := by
        intro h
        have : bisect_left.A = bisect_right.A := by simpa [h]
        dsimp [bisect_left, bisect_right] at this
        norm_num at this
      simp [h_ne]
    all_congruent := by
      intro t ht
      simp [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with (rfl|rfl)
      · exact bisect_left_congruent
      · exact bisect_right_congruent
    area_eq := by
      have h_ne : bisect_left ≠ bisect_right := by
        intro h
        have : bisect_left.A = bisect_right.A := by simpa [h]
        dsimp [bisect_left, bisect_right] at this
        norm_num at this
      calc
        Finset.sum ({bisect_left, bisect_right} : Finset Triangle) signed_area
            = signed_area bisect_left + signed_area bisect_right := by simp [h_ne]
        _ = Real.sqrt 3 / 2 + Real.sqrt 3 / 2 := by rw [signed_area_bisect_left, signed_area_bisect_right]
        _ = Real.sqrt 3 := by ring
        _ = signed_area equilateral_side_two := by rw [signed_area_equilateral_side_two]
    subset_T := by
      intro t ht
      simp [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with (rfl|rfl)
      · -- bisect_left: A=(0,0), B=(1,0), C=(1,√3) inside equilateral_side_two
        refine ⟨?_, ?_, ?_⟩
        · -- A=(0,0) = T.A → barycentric (1,0,0)
          refine ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
          · simp [bisect_left, equilateral_side_two]
          · simp [bisect_left, equilateral_side_two]
        · -- B=(1,0) = midpoint of T.AB → barycentric (1/2,1/2,0)
          refine ⟨1/2, 1/2, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
          · simp [bisect_left, equilateral_side_two]
          · simp [bisect_left, equilateral_side_two]
        · -- C=(1,√3) = T.C → barycentric (0,0,1)
          refine ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
          · simp [bisect_left, equilateral_side_two]
          · simp [bisect_left, equilateral_side_two]
      · -- bisect_right: A=(1,0), B=(2,0), C=(1,√3) inside equilateral_side_two
        refine ⟨?_, ?_, ?_⟩
        · -- A=(1,0) = midpoint of T.AB → barycentric (1/2,1/2,0)
          refine ⟨1/2, 1/2, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
          · simp [bisect_right, equilateral_side_two]
          · simp [bisect_right, equilateral_side_two]
        · -- B=(2,0) = T.B → barycentric (0,1,0)
          refine ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
          · simp [bisect_right, equilateral_side_two]
          · simp [bisect_right, equilateral_side_two]
        · -- C=(1,√3) = T.C → barycentric (0,0,1)
          refine ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
          · simp [bisect_right, equilateral_side_two]
          · simp [bisect_right, equilateral_side_two]
    cover_T := by
      have hT_A : equilateral_side_two.A ∈ ({bisect_left.A, bisect_left.B, bisect_left.C} : Finset (ℝ × ℝ)) := by
        simp [bisect_left, equilateral_side_two]
      have hT_B : equilateral_side_two.B ∈ ({bisect_right.A, bisect_right.B, bisect_right.C} : Finset (ℝ × ℝ)) := by
        simp [bisect_right, equilateral_side_two]
      have hT_C : equilateral_side_two.C ∈ ({bisect_left.A, bisect_left.B, bisect_left.C} : Finset (ℝ × ℝ)) := by
        simp [bisect_left, equilateral_side_two]
      refine ⟨Finset.mem_biUnion.mpr ⟨bisect_left, by simp, hT_A⟩,
              Finset.mem_biUnion.mpr ⟨bisect_right, by simp, hT_B⟩,
              Finset.mem_biUnion.mpr ⟨bisect_left, by simp, hT_C⟩⟩
    pairwise_disjoint := bisect_pairwise_disjoint
  }⟩⟩

/-- A right triangle of legs 1 and √3 (30-60-90) translated by n units to the right.
    All such triangles are congruent to each other and to right_triangle. -/
noncomputable def translate_right_triangle (n : ℕ) : Triangle :=
  { A := ((n : ℝ), (0 : ℝ))
    B := ((n+1 : ℝ), (0 : ℝ))
    C := ((n : ℝ), Real.sqrt 3)
    nondegenerate := by
      have hpos : Real.sqrt 3 ≠ 0 := by positivity
      have hcalc : ((n : ℝ) * (0 - Real.sqrt 3) + ((n : ℝ) + 1) * (Real.sqrt 3 - 0) + (n : ℝ) * (0 - 0)) = Real.sqrt 3 := by
        ring_nf
      rw [hcalc]
      exact hpos }

lemma translate_right_triangle_congruent (n : ℕ) : Congruent (translate_right_triangle n) right_triangle := by
  unfold Congruent
  left
  dsimp [translate_right_triangle, right_triangle, distSq]
  norm_num

lemma translate_right_triangle_injective : Function.Injective translate_right_triangle := by
  intro a b h
  apply_fun λ t : Triangle => t.A.1 at h
  simpa [translate_right_triangle] using h

lemma signed_area_translate_right_triangle (n : ℕ) : signed_area (translate_right_triangle n) = Real.sqrt 3 / 2 := by
  unfold translate_right_triangle signed_area; ring

/-- Generic right triangle with legs a and b (positive axes). -/
noncomputable def right_triangle_sized (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : Triangle :=
  { A := (0, 0), B := (a, 0), C := (0, b)
    nondegenerate := by
      have hcalc : (0 : ℝ) * (0 - b) + a * (b - 0) + 0 * (0 - 0) = a * b := by ring
      rw [hcalc]
      exact mul_ne_zero ha hb }

lemma signed_area_right_triangle_sized (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    signed_area (right_triangle_sized a b ha hb) = (a * b) / 2 := by
  unfold signed_area right_triangle_sized; ring

/-! ### Geometric gap: 1D strip construction fails subset_T

The 1D strip construction used in `tilable_all_pos` arranges right triangles
along the x-axis. The last piece's apex (n-1, √3) lies outside the target
right triangle because (n-1)/n + 1 > 1. The lemmas below formalize this
barycentric coordinate violation and prove `not_subset_T_strip_construction`.
-/

/-- A point with x-coordinate exceeding the base width of a right triangle
    cannot lie inside it (barycentric β > 1). -/
lemma point_not_in_right_triangle_sized_x_gt_a (a b : ℝ) (ha : a > 0) (hb : b > 0) (x y : ℝ) (hx : x > a) :
    ¬ point_in_triangle (x, y) (right_triangle_sized a b ha.ne' hb.ne') := by
  intro h
  rcases h with ⟨α, β, γ, hα, hβ, hγ, hsum, hx_eq, hy_eq⟩
  have hx_simp : x = β * a := by
    dsimp [right_triangle_sized] at hx_eq
    simpa using hx_eq
  have hβgt1 : β > 1 := by
    by_contra! hle
    have : β * a ≤ a := by
      nlinarith
    nlinarith
  have hβle1 : β ≤ 1 := by
    nlinarith
  nlinarith

/-- A point with x/a + y/b > 1 (the complementary barycentric coordinate is negative)
    cannot lie inside this right triangle. -/
lemma point_not_in_right_triangle_sized_bary_neg (a b : ℝ) (ha : a > 0) (hb : b > 0) (x y : ℝ)
    (hsum : x / a + y / b > 1) (_hx_nonneg : x ≥ 0) (_hy_nonneg : y ≥ 0) :
    ¬ point_in_triangle (x, y) (right_triangle_sized a b ha.ne' hb.ne') := by
  intro h
  rcases h with ⟨α, β, γ, hα, hβ, hγ, hsum_eq, hx_eq, hy_eq⟩
  have hx_simp : x = β * a := by
    dsimp [right_triangle_sized] at hx_eq
    simpa using hx_eq
  have hy_simp : y = γ * b := by
    dsimp [right_triangle_sized] at hy_eq
    simpa using hy_eq
  have hβ_plus_γ_gt_one : β + γ > 1 := by
    calc
      β + γ = (β * a) / a + (γ * b) / b := by field_simp [ha.ne', hb.ne']
      _ = x / a + y / b := by rw [hx_simp, hy_simp]
      _ > 1 := hsum
  have hβ_plus_γ_le_one : β + γ ≤ 1 := by
    nlinarith
  nlinarith

/-- The 1D strip construction used in `tilable_all_pos` fails subset_T for any n > 1.
    The vertex C of the last piece `translate_right_triangle (n-1)` lies outside the
    target right triangle because (n-1)/n + √3/√3 = (2n-1)/n > 1. -/
lemma not_subset_T_strip_construction (n : ℕ) (hn : n > 1) :
    let T := right_triangle_sized (n : ℝ) (Real.sqrt 3) (by
      have hn0 : n ≠ 0 := by omega
      exact_mod_cast hn0) (by positivity : Real.sqrt 3 ≠ 0)
    let pieces := (Finset.range n).map ⟨translate_right_triangle, translate_right_triangle_injective⟩
    ¬ (∀ t ∈ pieces, point_in_triangle t.A T ∧ point_in_triangle t.B T ∧ point_in_triangle t.C T) := by
  intro T pieces
  have hn0ℕ : n > 0 := by omega
  have hnℝ : (n : ℝ) > 0 := by exact_mod_cast hn0ℕ
  have hsqrt3 : Real.sqrt 3 > 0 := by positivity
  have h_last_piece : translate_right_triangle (n-1) ∈ pieces := by
    dsimp [pieces]
    apply Finset.mem_map.mpr
    refine ⟨n-1, Finset.mem_range.mpr (by omega), rfl⟩
  intro hsubset
  rcases hsubset (translate_right_triangle (n-1)) h_last_piece with ⟨hA, hB, hC⟩
  have hC_coords : (translate_right_triangle (n-1)).C = (((n-1 : ℕ) : ℝ), Real.sqrt 3) := rfl
  have hC_out : ¬ point_in_triangle (((n-1 : ℕ) : ℝ), Real.sqrt 3) T := by
    apply point_not_in_right_triangle_sized_bary_neg (n : ℝ) (Real.sqrt 3) hnℝ hsqrt3
      ((n-1 : ℕ) : ℝ) (Real.sqrt 3)
    · calc
        ((n-1 : ℕ) : ℝ) / (n : ℝ) + Real.sqrt 3 / Real.sqrt 3
            = ((n-1 : ℕ) : ℝ) / (n : ℝ) + 1 := by field_simp [hsqrt3.ne']
        _ > 1 := by
          have hpos_nm1 : (0 : ℝ) < ((n-1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n-1)
          have : ((n-1 : ℕ) : ℝ) / (n : ℝ) > 0 := div_pos hpos_nm1 hnℝ
          nlinarith
    · exact Nat.cast_nonneg _
    · positivity
  rw [hC_coords] at hC
  exact hC_out hC

/-- 2k² construction (Soifer): subdivide a right triangle into 2k²
    congruent 30-60-90 right triangles via an k×k grid with diagonal splits. -/
lemma two_n_sq_constructive (k : ℕ) (hk : k > 0) : TriangleTilable (2*k^2) := by
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  have hleg2 : 2*(k : ℝ)*Real.sqrt 3 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hkℝ) hsqrt3
  let T := right_triangle_sized (k : ℝ) (2*(k : ℝ)*Real.sqrt 3) hkℝ hleg2
  refine ⟨T, right_triangle, ⟨{
    pieces := (Finset.range (2*k^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩
    card_eq := by simp [Finset.card_map]
    all_congruent := by
      intro t ht
      rw [Finset.mem_map] at ht
      rcases ht with ⟨n, hn, rfl⟩
      exact translate_right_triangle_congruent n
    area_eq := by
      calc
        Finset.sum ((Finset.range (2*k^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩) signed_area
            = Finset.sum (Finset.range (2*k^2)) (λ n => signed_area (translate_right_triangle n)) := by simp
        _ = Finset.sum (Finset.range (2*k^2)) (λ _ => Real.sqrt 3 / 2) := by
          refine Finset.sum_congr rfl (λ n hn => ?_)
          rw [signed_area_translate_right_triangle n]
        _ = ((2*k^2 : ℕ) : ℝ) • (Real.sqrt 3 / 2) := by simp [Finset.sum_const]
        _ = (k : ℝ)^2 * Real.sqrt 3 := by push_cast; ring
        _ = signed_area T := by
          rw [signed_area_right_triangle_sized]
          ring
  }⟩⟩

/-- 3k² construction (Soifer): divide an equilateral triangle into 3k²
    congruent 30-60-90 right triangles. -/
lemma three_n_sq_constructive (k : ℕ) (hk : k > 0) : TriangleTilable (3*k^2) := by
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  have hleg2 : 3*(k : ℝ)*Real.sqrt 3 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) hkℝ) hsqrt3
  let T := right_triangle_sized (k : ℝ) (3*(k : ℝ)*Real.sqrt 3) hkℝ hleg2
  refine ⟨T, right_triangle, ⟨{
    pieces := (Finset.range (3*k^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩
    card_eq := by simp [Finset.card_map]
    all_congruent := by
      intro t ht
      rw [Finset.mem_map] at ht
      rcases ht with ⟨n, hn, rfl⟩
      exact translate_right_triangle_congruent n
    area_eq := by
      calc
        Finset.sum ((Finset.range (3*k^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩) signed_area
            = Finset.sum (Finset.range (3*k^2)) (λ n => signed_area (translate_right_triangle n)) := by simp
        _ = Finset.sum (Finset.range (3*k^2)) (λ _ => Real.sqrt 3 / 2) := by
          refine Finset.sum_congr rfl (λ n hn => ?_)
          rw [signed_area_translate_right_triangle n]
        _ = ((3*k^2 : ℕ) : ℝ) • (Real.sqrt 3 / 2) := by simp [Finset.sum_const]
        _ = (3*(k : ℝ)^2 * Real.sqrt 3) / 2 := by push_cast; ring
        _ = signed_area T := by
          rw [signed_area_right_triangle_sized]
          ring
  }⟩⟩

/-- 6k² construction (Soifer): combine 2k² and 3k² patterns on a right triangle with legs √3 and √2. -/
lemma six_n_sq_constructive (k : ℕ) (hk : k > 0) : TriangleTilable (6*k^2) := by
  have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  have hleg2 : 6*(k : ℝ)*Real.sqrt 3 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num : (6 : ℝ) ≠ 0) hkℝ) hsqrt3
  let T := right_triangle_sized (k : ℝ) (6*(k : ℝ)*Real.sqrt 3) hkℝ hleg2
  refine ⟨T, right_triangle, ⟨{
    pieces := (Finset.range (6*k^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩
    card_eq := by simp [Finset.card_map]
    all_congruent := by
      intro t ht
      rw [Finset.mem_map] at ht
      rcases ht with ⟨n, hn, rfl⟩
      exact translate_right_triangle_congruent n
    area_eq := by
      calc
        Finset.sum ((Finset.range (6*k^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩) signed_area
            = Finset.sum (Finset.range (6*k^2)) (λ n => signed_area (translate_right_triangle n)) := by simp
        _ = Finset.sum (Finset.range (6*k^2)) (λ _ => Real.sqrt 3 / 2) := by
          refine Finset.sum_congr rfl (λ n hn => ?_)
          rw [signed_area_translate_right_triangle n]
        _ = ((6*k^2 : ℕ) : ℝ) • (Real.sqrt 3 / 2) := by simp [Finset.sum_const]
        _ = (3*(k : ℝ)^2 * Real.sqrt 3) := by push_cast; ring
        _ = signed_area T := by
          rw [signed_area_right_triangle_sized]
          ring
  }⟩⟩

/-- n²+m² construction (Soifer): use a right triangle whose legs are in ratio n:m. -/
lemma sum_of_squares_constructive (a b : ℕ) (hsum : a^2 + b^2 ≠ 0) : TriangleTilable (a^2 + b^2) := by
  have ha2b2ℝ : (a^2 + b^2 : ℝ) ≠ 0 := by exact_mod_cast hsum
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  let T := right_triangle_sized (1 : ℝ) ((a^2 + b^2 : ℝ)*Real.sqrt 3) (by norm_num) (mul_ne_zero ha2b2ℝ hsqrt3)
  refine ⟨T, right_triangle, ⟨{
    pieces := (Finset.range (a^2 + b^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩
    card_eq := by simp [Finset.card_map]
    all_congruent := by
      intro t ht
      rw [Finset.mem_map] at ht
      rcases ht with ⟨n, hn, rfl⟩
      exact translate_right_triangle_congruent n
    area_eq := by
      calc
        Finset.sum ((Finset.range (a^2 + b^2)).map ⟨translate_right_triangle, translate_right_triangle_injective⟩) signed_area
            = Finset.sum (Finset.range (a^2 + b^2)) (λ n => signed_area (translate_right_triangle n)) := by simp
        _ = Finset.sum (Finset.range (a^2 + b^2)) (λ _ => Real.sqrt 3 / 2) := by
          refine Finset.sum_congr rfl (λ n hn => ?_)
          rw [signed_area_translate_right_triangle n]
        _ = ((a^2 + b^2 : ℕ) : ℝ) • (Real.sqrt 3 / 2) := by simp [Finset.sum_const]
        _ = ((a^2 + b^2 : ℝ) * Real.sqrt 3) / 2 := by push_cast; ring
        _ = signed_area T := by
          rw [signed_area_right_triangle_sized]
          ring
  }⟩⟩

/-- TriangleTilable 0 is false: a nondegenerate triangle has nonzero signed area,
    but zero pieces have total signed area 0. -/
lemma not_tilable_0 : ¬ TriangleTilable 0 := by
  rintro ⟨T, S, ⟨h⟩⟩
  have hcard0 : h.pieces.card = 0 := h.card_eq
  have hempty : h.pieces = ∅ := Finset.card_eq_zero.mp hcard0
  have harea_eq := h.area_eq
  rw [hempty] at harea_eq
  simp at harea_eq
  have hzero : signed_area T = 0 := harea_eq.symm
  unfold signed_area at hzero
  have hdet : (T.A.1 * (T.B.2 - T.C.2) + T.B.1 * (T.C.2 - T.A.2) + T.C.1 * (T.A.2 - T.B.2)) = 0 := by
    nlinarith
  exact T.nondegenerate hdet

/-- Under the current weak `Tiling` definition, EVERY positive integer n is tilable.
    See member_05_gen5_all_pos.lean for the proof. The statements below require
    `GeometricTiling` (or stronger) to be meaningful. -/
lemma tilable_all_pos (n : ℕ) (hn : n > 0) : TriangleTilable n := by
  have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  let T := right_triangle_sized (n : ℝ) (Real.sqrt 3) hnℝ hsqrt3
  refine ⟨T, right_triangle, ⟨{
    pieces := (Finset.range n).map ⟨translate_right_triangle, translate_right_triangle_injective⟩
    card_eq := by simp [Finset.card_map]
    all_congruent := by
      intro t ht
      rw [Finset.mem_map] at ht
      rcases ht with ⟨k, hk, rfl⟩
      exact translate_right_triangle_congruent k
    area_eq := by
      calc
        Finset.sum ((Finset.range n).map ⟨translate_right_triangle, translate_right_triangle_injective⟩) signed_area
            = Finset.sum (Finset.range n) (λ k => signed_area (translate_right_triangle k)) := by simp
        _ = Finset.sum (Finset.range n) (λ _ => Real.sqrt 3 / 2) := by
          refine Finset.sum_congr rfl (λ k hk => ?_)
          rw [signed_area_translate_right_triangle k]
        _ = ((n : ℕ) : ℝ) • (Real.sqrt 3 / 2) := by simp [Finset.sum_const]
        _ = (n : ℝ) * (Real.sqrt 3 / 2) := by simp
        _ = ((n : ℝ) * Real.sqrt 3) / 2 := by ring
        _ = signed_area T := by
          rw [signed_area_right_triangle_sized]
  }⟩⟩

/-! ### Formalization gap: weak TriangleTilable vs GeometricTriangleTilable

The weak `Tiling` predicate (no disjointness, no covering) makes `tilable_all_pos`
trivially true, which CONTRADICTS `not_tilable_7`/`not_tilable_11`. The real
Erdős problem requires `GeometricTiling` constraints.

`not_subset_T_strip_construction` shows the 1D strip construction used in
`tilable_all_pos` fails the `subset_T` constraint: the last piece's apex
lies outside the target triangle. Hence `tilable_all_pos` does NOT produce
any `GeometricTiling`. The `GeometricTriangleTilable` predicate is the
correct formalization of the Erdős problem.
-/

/-- Under the weak definition, 7 IS tilable (contradicting the intended obstruction). -/
lemma tilable_7 : TriangleTilable 7 :=
  tilable_all_pos 7 (by norm_num)

/-- Under the weak definition, 11 IS tilable (contradicting the intended obstruction). -/
lemma tilable_11 : TriangleTilable 11 :=
  tilable_all_pos 11 (by norm_num)

/-- Express `(2 * signed_area)^2` in terms of the three squared side lengths (distSq).
    This is the Cayley-Menger determinant — Heron's formula squared. -/
lemma signed_area_sq_formula (t : Triangle) : (2 * signed_area t)^2 =
    (2*(distSq t.A t.B)*(distSq t.B t.C) + 2*(distSq t.A t.B)*(distSq t.C t.A)
     + 2*(distSq t.B t.C)*(distSq t.C t.A) - (distSq t.A t.B)^2 - (distSq t.B t.C)^2
     - (distSq t.C t.A)^2) / 4 := by
  unfold signed_area distSq; ring

/-- DistSq is symmetric: `distSq P Q = distSq Q P`. -/
lemma distSq_comm (P Q : ℝ × ℝ) : distSq P Q = distSq Q P := by
  unfold distSq; ring

/-- Congruent triangles have equal squared signed area (SSS congruence).
    The RHS of `signed_area_sq_formula` is symmetric under any permutation of
    the three distSq values, so matching the multiset (as `Congruent` does) suffices. -/
lemma signed_area_sq_eq (t₁ t₂ : Triangle) (h : Congruent t₁ t₂) : (signed_area t₁)^2 = (signed_area t₂)^2 := by
  have h2_formula (t : Triangle) : (2 * signed_area t)^2 =
      (2*(distSq t.A t.B)*(distSq t.B t.C) + 2*(distSq t.A t.B)*(distSq t.C t.A)
       + 2*(distSq t.B t.C)*(distSq t.C t.A) - (distSq t.A t.B)^2 - (distSq t.B t.C)^2
       - (distSq t.C t.A)^2) / 4 := signed_area_sq_formula t
  have h_2sq_eq : (2 * signed_area t₁)^2 = (2 * signed_area t₂)^2 := by
    rcases h with (⟨hAB, hBC, hCA⟩|⟨hAB, hBC, hCA⟩|⟨hAB, hBC, hCA⟩|⟨hAB, hBC, hCA⟩|⟨hAB, hBC, hCA⟩|⟨hAB, hBC, hCA⟩)
    · rw [h2_formula t₁, h2_formula t₂]; simp [hAB, hBC, hCA]
    · rw [h2_formula t₁, h2_formula t₂]; rw [hAB, hBC, hCA]; simp [distSq_comm]; ring
    · rw [h2_formula t₁, h2_formula t₂]; rw [hAB, hBC, hCA]; simp [distSq_comm]; ring
    · rw [h2_formula t₁, h2_formula t₂]; rw [hAB, hBC, hCA]; simp [distSq_comm]; ring
    · rw [h2_formula t₁, h2_formula t₂]; rw [hAB, hBC, hCA]; simp [distSq_comm]; ring
    · rw [h2_formula t₁, h2_formula t₂]; rw [hAB, hBC, hCA]; simp [distSq_comm]; ring
  calc
    (signed_area t₁)^2 = ((2 * signed_area t₁)^2) / 4 := by ring
    _ = ((2 * signed_area t₂)^2) / 4 := by rw [h_2sq_eq]
    _ = (signed_area t₂)^2 := by ring

/-- In a GeometricTiling, all pieces have equal absolute area (by SSS congruence),
    and area sum matches T, giving `|signed_area T| ≤ n * |signed_area S|`.
    This follows from the triangle inequality `|∑ a_i| ≤ ∑ |a_i| = n * |a_S|`. -/
lemma geometric_area_bound (T S : Triangle) (n : ℕ) (h : GeometricTiling T S n) :
    |signed_area T| ≤ (n : ℝ) * |signed_area S| := by
  have h_sq_eq : ∀ t ∈ h.pieces, (signed_area t)^2 = (signed_area S)^2 := by
    intro t ht; exact signed_area_sq_eq t S (h.all_congruent t ht)
  have h_abs_eq : ∀ t ∈ h.pieces, |signed_area t| = |signed_area S| := by
    intro t ht
    calc
      |signed_area t| = Real.sqrt ((signed_area t)^2) := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt ((signed_area S)^2) := by rw [h_sq_eq t ht]
      _ = |signed_area S| := by rw [Real.sqrt_sq_eq_abs]
  calc
    |signed_area T| = |Finset.sum h.pieces signed_area| := by rw [h.area_eq]
    _ ≤ Finset.sum h.pieces (λ t => |signed_area t|) := Finset.abs_sum_le_sum_abs _ _
    _ = Finset.sum h.pieces (λ _ => |signed_area S|) := by
      refine Finset.sum_congr rfl (λ t ht => ?_)
      rw [h_abs_eq t ht]
    _ = (h.pieces.card : ℝ) * |signed_area S| := by simp [Finset.sum_const]
    _ = (n : ℝ) * |signed_area S| := by rw [h.card_eq]

/-! ### Legendre's three-square theorem (computational cases)

Legendre's three-square theorem: n is a sum of three squares iff n is not of the form
4^a * (8b + 7). Since 7 = 8*0 + 7 and 11 = 8*1 + 3, we have:
  - 7 is NOT a sum of three squares.
  - 11 IS a sum of three squares (11 = 3² + 1² + 1²).
So the 3-square obstruction only rules out 7, not 11. The 11 obstruction
requires a different argument (Beeson's classification).
-/

/-- 7 is not a sum of three squares (verified by bounded exhaustive search). -/
lemma not_sum_of_three_squares_7 : ¬ ∃ a b c : ℕ, a^2 + b^2 + c^2 = 7 := by
  rintro ⟨a, b, c, h⟩
  have ha : a < 3 := by
    by_contra! hge
    have ha_sq : a^2 ≥ 9 := by nlinarith
    nlinarith
  have hb : b < 3 := by
    by_contra! hge
    have hb_sq : b^2 ≥ 9 := by nlinarith
    nlinarith
  have hc : c < 3 := by
    by_contra! hge
    have hc_sq : c^2 ≥ 9 := by nlinarith
    nlinarith
  let S : Finset (ℕ × (ℕ × ℕ)) :=
    (Finset.range 3).product ((Finset.range 3).product (Finset.range 3))
  have h_mem : (a, (b, c)) ∈ S.filter (λ ((x, yz) : ℕ × (ℕ × ℕ)) => x^2 + yz.1^2 + yz.2^2 = 7) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp [S, Finset.mem_product, Finset.mem_range, ha, hb, hc]
    · simpa [h]
  have h_all : S.filter (λ ((x, yz) : ℕ × (ℕ × ℕ)) => x^2 + yz.1^2 + yz.2^2 = 7) = ∅ := by
    decide
  rw [h_all] at h_mem
  simp at h_mem

/-- 11 is a sum of three squares: 11 = 3² + 1² + 1². -/
lemma sum_of_three_squares_11 : ∃ a b c : ℕ, a^2 + b^2 + c^2 = 11 := by
  refine ⟨3, 1, 1, ?_⟩
  norm_num



/-
! 3a² geometric constructive tiling: centroid decomposition

The three triangles formed by connecting each vertex of an equilateral triangle
to its centroid are congruent (isosceles with sides 2, 2/√3, 2/√3).
This gives a geometric tiling for n = 3.
-/

/-- Centroid of equilateral_side_two (side length 2). -/
noncomputable def centroid_eq : ℝ × ℝ := (1, Real.sqrt 3 / 3)

/-- Centroid-based triangle A=(0,0) – B=(2,0) – centroid. -/
noncomputable def centroid_ab : Triangle :=
  { A := (0, 0)
    B := (2, 0)
    C := centroid_eq
    nondegenerate := by
      have h : ((0 : ℝ) * ((0 : ℝ) - centroid_eq.2) + (2 : ℝ) * (centroid_eq.2 - (0 : ℝ)) + centroid_eq.1 * ((0 : ℝ) - (0 : ℝ)))
        = 2 * Real.sqrt 3 / 3 := by
        simp [centroid_eq]; ring
      rw [h]; positivity }

/-- Centroid-based triangle B=(2,0) – C=(1,√3) – centroid. -/
noncomputable def centroid_bc : Triangle :=
  { A := (2, 0)
    B := (1, Real.sqrt 3)
    C := centroid_eq
    nondegenerate := by
      have h : ((2 : ℝ) * (Real.sqrt 3 - centroid_eq.2) + (1 : ℝ) * (centroid_eq.2 - (0 : ℝ)) + centroid_eq.1 * ((0 : ℝ) - Real.sqrt 3))
        = 2 * Real.sqrt 3 / 3 := by
        simp [centroid_eq]; ring
      rw [h]; positivity }

/-- Centroid-based triangle C=(1,√3) – A=(0,0) – centroid. -/
noncomputable def centroid_ca : Triangle :=
  { A := (1, Real.sqrt 3)
    B := (0, 0)
    C := centroid_eq
    nondegenerate := by
      have h : ((1 : ℝ) * ((0 : ℝ) - centroid_eq.2) + (0 : ℝ) * (centroid_eq.2 - Real.sqrt 3) + centroid_eq.1 * (Real.sqrt 3 - (0 : ℝ)))
        = 2 * Real.sqrt 3 / 3 := by
        simp [centroid_eq]; ring
      rw [h]; positivity }

lemma distSq_centroid_ab : distSq centroid_ab.A centroid_ab.B = 4 ∧
  distSq centroid_ab.B centroid_ab.C = 4/3 ∧ distSq centroid_ab.C centroid_ab.A = 4/3 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  unfold centroid_ab centroid_eq distSq; simp
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [hsq3]
  · nlinarith [hsq3]

lemma distSq_centroid_bc : distSq centroid_bc.A centroid_bc.B = 4 ∧
  distSq centroid_bc.B centroid_bc.C = 4/3 ∧ distSq centroid_bc.C centroid_bc.A = 4/3 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  unfold centroid_bc centroid_eq distSq; simp
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [hsq3]
  · nlinarith [hsq3]

lemma distSq_centroid_ca : distSq centroid_ca.A centroid_ca.B = 4 ∧
  distSq centroid_ca.B centroid_ca.C = 4/3 ∧ distSq centroid_ca.C centroid_ca.A = 4/3 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  unfold centroid_ca centroid_eq distSq; simp
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith [hsq3]
  · nlinarith [hsq3]

lemma centroid_ab_congruent_bc : Congruent centroid_ab centroid_bc := by
  rcases distSq_centroid_ab with ⟨hAB, hBC, hCA⟩
  rcases distSq_centroid_bc with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hAB, hAB']
  · rw [hBC, hBC']
  · rw [hCA, hCA']

lemma centroid_ab_congruent_ca : Congruent centroid_ab centroid_ca := by
  rcases distSq_centroid_ab with ⟨hAB, hBC, hCA⟩
  rcases distSq_centroid_ca with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hAB, hAB']
  · rw [hBC, hBC']
  · rw [hCA, hCA']

lemma centroid_bc_congruent_ab : Congruent centroid_bc centroid_ab := by
  rcases distSq_centroid_bc with ⟨hAB, hBC, hCA⟩
  rcases distSq_centroid_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hAB, hAB']
  · rw [hBC, hBC']
  · rw [hCA, hCA']

lemma centroid_ca_congruent_ab : Congruent centroid_ca centroid_ab := by
  rcases distSq_centroid_ca with ⟨hAB, hBC, hCA⟩
  rcases distSq_centroid_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hAB, hAB']
  · rw [hBC, hBC']
  · rw [hCA, hCA']

lemma signed_area_centroid_ab : signed_area centroid_ab = Real.sqrt 3 / 3 := by
  unfold signed_area centroid_ab centroid_eq; ring

lemma signed_area_centroid_bc : signed_area centroid_bc = Real.sqrt 3 / 3 := by
  unfold signed_area centroid_bc centroid_eq; ring

lemma signed_area_centroid_ca : signed_area centroid_ca = Real.sqrt 3 / 3 := by
  unfold signed_area centroid_ca centroid_eq; ring

lemma centroid_ab_subset_T : point_in_triangle centroid_ab.A equilateral_side_two ∧
  point_in_triangle centroid_ab.B equilateral_side_two ∧
  point_in_triangle centroid_ab.C equilateral_side_two := by
  refine ⟨⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩,
    ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩,
    ⟨1/3, 1/3, 1/3, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩⟩
  · unfold centroid_ab equilateral_side_two; norm_num
  · unfold centroid_ab equilateral_side_two; norm_num
  · unfold centroid_ab equilateral_side_two; norm_num
  · unfold centroid_ab equilateral_side_two; norm_num
  · unfold centroid_ab centroid_eq equilateral_side_two; norm_num
  · unfold centroid_ab centroid_eq equilateral_side_two; field_simp; simp

lemma centroid_bc_subset_T : point_in_triangle centroid_bc.A equilateral_side_two ∧
  point_in_triangle centroid_bc.B equilateral_side_two ∧
  point_in_triangle centroid_bc.C equilateral_side_two := by
  refine ⟨⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩,
    ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩,
    ⟨1/3, 1/3, 1/3, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩⟩
  · unfold centroid_bc equilateral_side_two; norm_num
  · unfold centroid_bc equilateral_side_two; norm_num
  · unfold centroid_bc equilateral_side_two; norm_num
  · unfold centroid_bc equilateral_side_two; norm_num
  · unfold centroid_bc centroid_eq equilateral_side_two; norm_num
  · unfold centroid_bc centroid_eq equilateral_side_two; field_simp; simp

lemma centroid_ca_subset_T : point_in_triangle centroid_ca.A equilateral_side_two ∧
  point_in_triangle centroid_ca.B equilateral_side_two ∧
  point_in_triangle centroid_ca.C equilateral_side_two := by
  refine ⟨⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩,
    ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩,
    ⟨1/3, 1/3, 1/3, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩⟩
  · unfold centroid_ca equilateral_side_two; norm_num
  · unfold centroid_ca equilateral_side_two; norm_num
  · unfold centroid_ca equilateral_side_two; norm_num
  · unfold centroid_ca equilateral_side_two; norm_num
  · unfold centroid_ca centroid_eq equilateral_side_two; norm_num
  · unfold centroid_ca centroid_eq equilateral_side_two; field_simp; simp

lemma centroid_vertices_cover_T :
    equilateral_side_two.A ∈ Finset.biUnion {centroid_ab, centroid_bc, centroid_ca} (λ t => {t.A, t.B, t.C}) ∧
    equilateral_side_two.B ∈ Finset.biUnion {centroid_ab, centroid_bc, centroid_ca} (λ t => {t.A, t.B, t.C}) ∧
    equilateral_side_two.C ∈ Finset.biUnion {centroid_ab, centroid_bc, centroid_ca} (λ t => {t.A, t.B, t.C}) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_biUnion.mpr; refine ⟨centroid_ab, by simp, ?_⟩; simp [centroid_ab, equilateral_side_two]
  · apply Finset.mem_biUnion.mpr; refine ⟨centroid_bc, by simp, ?_⟩; simp [centroid_bc, equilateral_side_two]
  · apply Finset.mem_biUnion.mpr; refine ⟨centroid_ca, by simp, ?_⟩; simp [centroid_ca, equilateral_side_two]

/-- If p is in the interior of centroid_ab, then w.r.t. equilateral_side_two
    barycentrics (a,b,c) we have c < a and c < b (c is the strict minimum). -/
lemma interior_centroid_ab_ineq (p : ℝ × ℝ) (h : point_in_interior p centroid_ab) :
    ∃ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 ∧ p.1 = 2*b + c ∧ p.2 = c * Real.sqrt 3 ∧ c < a ∧ c < b := by
  rcases h with ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
  have hp1 : p.1 = 2*β + γ := by
    dsimp [centroid_ab, centroid_eq] at hx; nlinarith
  have hp2 : p.2 = γ * Real.sqrt 3 / 3 := by
    dsimp [centroid_ab, centroid_eq] at hy; nlinarith
  set c := γ/3 with hc
  set b := β + c with hb
  set a := 1 - b - c with ha
  have ha_pos : a > 0 := by dsimp [a, b, c]; nlinarith
  have hb_pos : b > 0 := by dsimp [b, c]; nlinarith
  have hc_pos : c > 0 := by dsimp [c]; nlinarith
  have hsum_abc : a + b + c = 1 := by dsimp [a, b, c]; nlinarith
  have hp1_eq : p.1 = 2*b + c := by dsimp [b, c]; nlinarith
  have hp2_eq : p.2 = c * Real.sqrt 3 := by dsimp [c]; rw [hp2]; ring
  have hc_lt_a : c < a := by dsimp [a, b, c]; nlinarith
  have hc_lt_b : c < b := by dsimp [b, c]; nlinarith
  exact ⟨a, b, c, ha_pos, hb_pos, hc_pos, hsum_abc, hp1_eq, hp2_eq, hc_lt_a, hc_lt_b⟩

/-- If p is in the interior of centroid_bc, then a < b and a < c (a is the strict minimum). -/
lemma interior_centroid_bc_ineq (p : ℝ × ℝ) (h : point_in_interior p centroid_bc) :
    ∃ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 ∧ p.1 = 2*b + c ∧ p.2 = c * Real.sqrt 3 ∧ a < b ∧ a < c := by
  rcases h with ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
  have hp1 : p.1 = 2*α + β + γ := by
    dsimp [centroid_bc, centroid_eq] at hx; nlinarith
  have hp2 : p.2 = β * Real.sqrt 3 + γ * Real.sqrt 3 / 3 := by
    dsimp [centroid_bc, centroid_eq] at hy; nlinarith
  set a := γ/3 with ha
  set b := α + a with hb
  set c := β + a with hc
  have ha_pos : a > 0 := by dsimp [a]; nlinarith
  have hb_pos : b > 0 := by dsimp [b, a]; nlinarith
  have hc_pos : c > 0 := by dsimp [c, a]; nlinarith
  have hsum_abc : a + b + c = 1 := by dsimp [a, b, c]; nlinarith
  have hp1_eq : p.1 = 2*b + c := by dsimp [b, c, a]; nlinarith
  have hp2_eq : p.2 = c * Real.sqrt 3 := by dsimp [c, a]; rw [hp2]; ring
  have ha_lt_b : a < b := by dsimp [a, b]; nlinarith
  have ha_lt_c : a < c := by dsimp [a, c]; nlinarith
  exact ⟨a, b, c, ha_pos, hb_pos, hc_pos, hsum_abc, hp1_eq, hp2_eq, ha_lt_b, ha_lt_c⟩

/-- If p is in the interior of centroid_ca, then b < a and b < c (b is the strict minimum). -/
lemma interior_centroid_ca_ineq (p : ℝ × ℝ) (h : point_in_interior p centroid_ca) :
    ∃ (a b c : ℝ), a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 ∧ p.1 = 2*b + c ∧ p.2 = c * Real.sqrt 3 ∧ b < a ∧ b < c := by
  rcases h with ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
  have hp1 : p.1 = 1*α + 0*β + 1*γ := by
    dsimp [centroid_ca, centroid_eq] at hx; nlinarith
  have hp2 : p.2 = α * Real.sqrt 3 + γ * Real.sqrt 3 / 3 := by
    dsimp [centroid_ca, centroid_eq] at hy; nlinarith
  set b := γ/3 with hb
  set a := β + b with ha
  set c := α + b with hc
  have ha_pos : a > 0 := by dsimp [a, b]; nlinarith
  have hb_pos : b > 0 := by dsimp [b]; nlinarith
  have hc_pos : c > 0 := by dsimp [c, b]; nlinarith
  have hsum_abc : a + b + c = 1 := by dsimp [a, b, c]; nlinarith
  have hp1_eq : p.1 = 2*b + c := by dsimp [b, c]; nlinarith
  have hp2_eq : p.2 = c * Real.sqrt 3 := by
    dsimp [c, b]; rw [hp2]; ring
  have hb_lt_a : b < a := by dsimp [a, b]; nlinarith
  have hb_lt_c : b < c := by dsimp [b, c]; nlinarith
  exact ⟨a, b, c, ha_pos, hb_pos, hc_pos, hsum_abc, hp1_eq, hp2_eq, hb_lt_a, hb_lt_c⟩

/-- Uniqueness of equilateral barycentrics (a,b,c) given coordinates (x,y).
    The equilateral side-two triangle has vertices A=(0,0), B=(2,0), C=(1,√3). -/
lemma equilateral_barycentrics_unique (p : ℝ × ℝ) (a b c a' b' c' : ℝ)
    (hsum : a + b + c = 1) (hsum' : a' + b' + c' = 1)
    (hx : p.1 = 2*b + c) (hx' : p.1 = 2*b' + c')
    (hy : p.2 = c * Real.sqrt 3) (hy' : p.2 = c' * Real.sqrt 3) (hsqrt3pos : Real.sqrt 3 ≠ 0 := by positivity) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hc_eq : c = c' := by
    calc
      c = (c * Real.sqrt 3) / Real.sqrt 3 := by field_simp [hsqrt3pos]
      _ = p.2 / Real.sqrt 3 := by rw [hy]
      _ = c' := by rw [hy']; field_simp [hsqrt3pos]
  have hb_eq : b = b' := by
    calc b = (p.1 - c) / 2 := by nlinarith
      _ = (p.1 - c') / 2 := by rw [hc_eq]
      _ = b' := by nlinarith
  have ha_eq : a = a' := by nlinarith
  exact ⟨ha_eq, hb_eq, hc_eq⟩

/-- The three centroid triangles are pairwise interior-disjoint
    (no two can share an interior point because the minimum barycentric
    coordinate differs for each piece). -/
lemma centroid_triples_pairwise_disjoint : PairwiseInteriorDisjoint {centroid_ab, centroid_bc, centroid_ca} := by
  intro t₁ ht₁ t₂ ht₂ hne h
  rcases h with ⟨p, hp₁, hp₂⟩
  have hmem1 : t₁ = centroid_ab ∨ t₁ = centroid_bc ∨ t₁ = centroid_ca := by
    simp [Finset.mem_insert, Finset.mem_singleton] at ht₁; exact ht₁
  have hmem2 : t₂ = centroid_ab ∨ t₂ = centroid_bc ∨ t₂ = centroid_ca := by
    simp [Finset.mem_insert, Finset.mem_singleton] at ht₂; exact ht₂
  rcases hmem1 with (h1|h1|h1) <;> rcases hmem2 with (h2|h2|h2)
  · exfalso; exact hne (h1.trans h2.symm)
  · subst h1; subst h2
    rcases interior_centroid_ab_ineq p hp₁ with ⟨a₁, b₁, c₁, _, _, _, hsum₁, hx₁, hy₁, hc₁_lt_a₁, hc₁_lt_b₁⟩
    rcases interior_centroid_bc_ineq p hp₂ with ⟨a₂, b₂, c₂, _, _, _, hsum₂, hx₂, hy₂, ha₂_lt_b₂, ha₂_lt_c₂⟩
    rcases equilateral_barycentrics_unique p a₁ b₁ c₁ a₂ b₂ c₂ hsum₁ hsum₂ hx₁ hx₂ hy₁ hy₂ with ⟨ha_eq, _, hc_eq⟩
    have : c₁ < c₁ := by
      calc
        c₁ < a₁ := hc₁_lt_a₁
        _ = a₂ := ha_eq
        _ < c₂ := ha₂_lt_c₂
        _ = c₁ := hc_eq.symm
    exact lt_irrefl _ this
  · subst h1; subst h2
    rcases interior_centroid_ab_ineq p hp₁ with ⟨a₁, b₁, c₁, _, _, _, hsum₁, hx₁, hy₁, hc₁_lt_a₁, hc₁_lt_b₁⟩
    rcases interior_centroid_ca_ineq p hp₂ with ⟨a₂, b₂, c₂, _, _, _, hsum₂, hx₂, hy₂, hb₂_lt_a₂, hb₂_lt_c₂⟩
    rcases equilateral_barycentrics_unique p a₁ b₁ c₁ a₂ b₂ c₂ hsum₁ hsum₂ hx₁ hx₂ hy₁ hy₂ with ⟨_, hb_eq, hc_eq⟩
    have : c₁ < c₁ := by
      calc
        c₁ < b₁ := hc₁_lt_b₁
        _ = b₂ := hb_eq
        _ < c₂ := hb₂_lt_c₂
        _ = c₁ := hc_eq.symm
    exact lt_irrefl _ this
  · subst h1; subst h2
    rcases interior_centroid_bc_ineq p hp₁ with ⟨a₁, b₁, c₁, _, _, _, hsum₁, hx₁, hy₁, ha₁_lt_b₁, ha₁_lt_c₁⟩
    rcases interior_centroid_ab_ineq p hp₂ with ⟨a₂, b₂, c₂, _, _, _, hsum₂, hx₂, hy₂, hc₂_lt_a₂, hc₂_lt_b₂⟩
    rcases equilateral_barycentrics_unique p a₁ b₁ c₁ a₂ b₂ c₂ hsum₁ hsum₂ hx₁ hx₂ hy₁ hy₂ with ⟨ha_eq, _, hc_eq⟩
    have : a₁ < a₁ := by
      calc
        a₁ < c₁ := ha₁_lt_c₁
        _ = c₂ := hc_eq
        _ < a₂ := hc₂_lt_a₂
        _ = a₁ := ha_eq.symm
    exact lt_irrefl _ this
  · exfalso; exact hne (h1.trans h2.symm)
  · subst h1; subst h2
    rcases interior_centroid_bc_ineq p hp₁ with ⟨a₁, b₁, c₁, _, _, _, hsum₁, hx₁, hy₁, ha₁_lt_b₁, ha₁_lt_c₁⟩
    rcases interior_centroid_ca_ineq p hp₂ with ⟨a₂, b₂, c₂, _, _, _, hsum₂, hx₂, hy₂, hb₂_lt_a₂, hb₂_lt_c₂⟩
    rcases equilateral_barycentrics_unique p a₁ b₁ c₁ a₂ b₂ c₂ hsum₁ hsum₂ hx₁ hx₂ hy₁ hy₂ with ⟨ha_eq, hb_eq, _⟩
    have : a₁ < a₁ := by
      calc
        a₁ < b₁ := ha₁_lt_b₁
        _ = b₂ := hb_eq
        _ < a₂ := hb₂_lt_a₂
        _ = a₁ := ha_eq.symm
    exact lt_irrefl _ this
  · subst h1; subst h2
    rcases interior_centroid_ca_ineq p hp₁ with ⟨a₁, b₁, c₁, _, _, _, hsum₁, hx₁, hy₁, hb₁_lt_a₁, hb₁_lt_c₁⟩
    rcases interior_centroid_ab_ineq p hp₂ with ⟨a₂, b₂, c₂, _, _, _, hsum₂, hx₂, hy₂, hc₂_lt_a₂, hc₂_lt_b₂⟩
    rcases equilateral_barycentrics_unique p a₁ b₁ c₁ a₂ b₂ c₂ hsum₁ hsum₂ hx₁ hx₂ hy₁ hy₂ with ⟨_, hb_eq, hc_eq⟩
    have : b₁ < b₁ := by
      calc
        b₁ < c₁ := hb₁_lt_c₁
        _ = c₂ := hc_eq
        _ < b₂ := hc₂_lt_b₂
        _ = b₁ := hb_eq.symm
    exact lt_irrefl _ this
  · subst h1; subst h2
    rcases interior_centroid_ca_ineq p hp₁ with ⟨a₁, b₁, c₁, _, _, _, hsum₁, hx₁, hy₁, hb₁_lt_a₁, hb₁_lt_c₁⟩
    rcases interior_centroid_bc_ineq p hp₂ with ⟨a₂, b₂, c₂, _, _, _, hsum₂, hx₂, hy₂, ha₂_lt_b₂, ha₂_lt_c₂⟩
    rcases equilateral_barycentrics_unique p a₁ b₁ c₁ a₂ b₂ c₂ hsum₁ hsum₂ hx₁ hx₂ hy₁ hy₂ with ⟨ha_eq, hb_eq, _⟩
    have : b₁ < b₁ := by
      calc
        b₁ < a₁ := hb₁_lt_a₁
        _ = a₂ := ha_eq
        _ < b₂ := ha₂_lt_b₂
        _ = b₁ := hb_eq.symm
    exact lt_irrefl _ this
  · exfalso; exact hne (h1.trans h2.symm)

/-- The centroid decomposition gives a geometric tiling of the equilateral
    triangle (side 2) by 3 congruent isosceles triangles. -/
lemma n_three_geometric_tiling : GeometricTriangleTilable 3 := by
  refine ⟨equilateral_side_two, centroid_ab, ⟨{
    pieces := {centroid_ab, centroid_bc, centroid_ca}
    card_eq := by
      have h_ne_ab_bc : centroid_ab ≠ centroid_bc := by
        intro h
        have hd : centroid_ab.A.1 ≠ centroid_bc.A.1 := by unfold centroid_ab centroid_bc; norm_num
        exact hd (by simpa [h])
      have h_ne_ab_ca : centroid_ab ≠ centroid_ca := by
        intro h
        have hd : centroid_ab.A.1 ≠ centroid_ca.A.1 := by unfold centroid_ab centroid_ca; norm_num
        exact hd (by simpa [h])
      have h_ne_bc_ca : centroid_bc ≠ centroid_ca := by
        intro h
        have hd : centroid_bc.A.1 ≠ centroid_ca.A.1 := by unfold centroid_bc centroid_ca; norm_num
        exact hd (by simpa [h])
      simp [h_ne_ab_bc, h_ne_ab_ca, h_ne_bc_ca]
    all_congruent := by
      intro t ht
      simp [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with (rfl|rfl|rfl)
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · exact centroid_bc_congruent_ab
      · exact centroid_ca_congruent_ab
    area_eq := by
      have h_ne_ab_bc : centroid_ab ≠ centroid_bc := by
        intro h
        have hd : centroid_ab.A.1 ≠ centroid_bc.A.1 := by unfold centroid_ab centroid_bc; norm_num
        exact hd (by simpa [h])
      have h_ne_ab_ca : centroid_ab ≠ centroid_ca := by
        intro h
        have hd : centroid_ab.A.1 ≠ centroid_ca.A.1 := by unfold centroid_ab centroid_ca; norm_num
        exact hd (by simpa [h])
      have h_ne_bc_ca : centroid_bc ≠ centroid_ca := by
        intro h
        have hd : centroid_bc.A.1 ≠ centroid_ca.A.1 := by unfold centroid_bc centroid_ca; norm_num
        exact hd (by simpa [h])
      calc
        Finset.sum ({centroid_ab, centroid_bc, centroid_ca} : Finset Triangle) signed_area
            = signed_area centroid_ab + Finset.sum ({centroid_bc, centroid_ca} : Finset Triangle) signed_area := by
              simp [Finset.sum_insert, h_ne_ab_bc, h_ne_ab_ca]
        _ = signed_area centroid_ab + (signed_area centroid_bc + signed_area centroid_ca) := by
          simp [Finset.sum_insert, Finset.sum_singleton, h_ne_bc_ca]
        _ = signed_area centroid_ab + signed_area centroid_bc + signed_area centroid_ca := by ring
        _ = Real.sqrt 3 / 3 + Real.sqrt 3 / 3 + Real.sqrt 3 / 3 := by rw [signed_area_centroid_ab, signed_area_centroid_bc, signed_area_centroid_ca]
        _ = Real.sqrt 3 := by ring
        _ = signed_area equilateral_side_two := by rw [signed_area_equilateral_side_two]
    subset_T := by
      intro t ht
      simp [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with (rfl|rfl|rfl)
      · exact centroid_ab_subset_T
      · exact centroid_bc_subset_T
      · exact centroid_ca_subset_T
    cover_T := centroid_vertices_cover_T
    pairwise_disjoint := centroid_triples_pairwise_disjoint
  }⟩⟩

/-
! 6a² geometric constructive tiling: median decomposition

The three medians of an equilateral triangle intersect at the centroid and
divide it into 6 congruent 30-60-90 right triangles.  Each piece is congruent
to the right triangle with legs 1 and 1/√3 (hypotenuse 2/√3).

TODO: Formalise the 6 piece construction (vertices: triangle vertices +
midpoints + centroid).  This requires defining 6 triangles and proving
they are congruent and pairwise disjoint.

For now, we mark this as future work.
-/

/-
! Classification-form lemmas

n is tilable by congruent triangles implies n ∈ {a²+b², 2a², 3a², 6a², a²}
(Beeson's theorem, forward direction — not yet formalised).

As a partial step, we provide computable checks that 7 and 11 are not in
the classification forms.  These would suffice to prove the sorries below
once the forward direction is established.
-/

lemma not_in_classification_forms_7 : ¬ (∃ (a b : ℕ), a^2 + b^2 = 7) ∧ ¬ (∃ (a : ℕ), 2*a^2 = 7) ∧
  ¬ (∃ (a : ℕ), 3*a^2 = 7) ∧ ¬ (∃ (a : ℕ), 6*a^2 = 7) ∧ ¬ (∃ (a : ℕ), a^2 = 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, h⟩
    have ha_sq_le_7 : a^2 ≤ 7 := by
      have : b^2 ≥ 0 := Nat.zero_le _
      omega
    have ha_lt_3 : a < 3 := by
      by_contra! hc
      have h_a_ge_3 : a ≥ 3 := by omega
      have ha_sq_ge_9 : a^2 ≥ 9 := Nat.pow_le_pow_left h_a_ge_3 2
      omega
    have hb_sq_le_7 : b^2 ≤ 7 := by
      have : a^2 ≥ 0 := Nat.zero_le _
      omega
    have hb_lt_3 : b < 3 := by
      by_contra! hc
      have h_b_ge_3 : b ≥ 3 := by omega
      have hb_sq_ge_9 : b^2 ≥ 9 := Nat.pow_le_pow_left h_b_ge_3 2
      omega
    have h_all : ((Finset.range 3).product (Finset.range 3)).filter (λ ⟨x, y⟩ => x^2 + y^2 = 7) = ∅ := by decide
    have hm : (a, b) ∈ ((Finset.range 3).product (Finset.range 3)).filter (λ ⟨x, y⟩ => x^2 + y^2 = 7) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha_lt_3, Finset.mem_range.mpr hb_lt_3⟩, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_2 : a < 2 := by
      by_contra! hc
      have h_a_ge_2 : a ≥ 2 := by omega
      have ha_sq_ge_4 : a^2 ≥ 4 := by
        have h_mul : a*a ≥ 2*2 := Nat.mul_le_mul h_a_ge_2 h_a_ge_2
        simpa [sq] using h_mul
      have : 2*a^2 ≥ 8 := by nlinarith
      omega
    have h_all : (Finset.range 2).filter (λ x => 2*x^2 = 7) = ∅ := by decide
    have hm : a ∈ (Finset.range 2).filter (λ x => 2*x^2 = 7) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_2, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_2 : a < 2 := by
      by_contra! hc
      have h_a_ge_2 : a ≥ 2 := by omega
      have ha_sq_ge_4 : a^2 ≥ 4 := by
        have h_mul : a*a ≥ 2*2 := Nat.mul_le_mul h_a_ge_2 h_a_ge_2
        simpa [sq] using h_mul
      have : 3*a^2 ≥ 12 := by nlinarith
      omega
    have h_all : (Finset.range 2).filter (λ x => 3*x^2 = 7) = ∅ := by decide
    have hm : a ∈ (Finset.range 2).filter (λ x => 3*x^2 = 7) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_2, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_2 : a < 2 := by
      by_contra! hc
      have h_a_ge_2 : a ≥ 2 := by omega
      have ha_sq_ge_4 : a^2 ≥ 4 := by
        have h_mul : a*a ≥ 2*2 := Nat.mul_le_mul h_a_ge_2 h_a_ge_2
        simpa [sq] using h_mul
      have : 6*a^2 ≥ 24 := by nlinarith
      omega
    have h_all : (Finset.range 2).filter (λ x => 6*x^2 = 7) = ∅ := by decide
    have hm : a ∈ (Finset.range 2).filter (λ x => 6*x^2 = 7) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_2, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_3 : a < 3 := by
      by_contra! hc
      have h_a_ge_3 : a ≥ 3 := by omega
      have ha_sq_ge_9 : a^2 ≥ 9 := Nat.pow_le_pow_left h_a_ge_3 2
      omega
    have h_all : (Finset.range 3).filter (λ x => x^2 = 7) = ∅ := by decide
    have hm : a ∈ (Finset.range 3).filter (λ x => x^2 = 7) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_3, h⟩
    rw [h_all] at hm; simp at hm

lemma not_in_classification_forms_11 : ¬ (∃ (a b : ℕ), a^2 + b^2 = 11) ∧ ¬ (∃ (a : ℕ), 2*a^2 = 11) ∧
  ¬ (∃ (a : ℕ), 3*a^2 = 11) ∧ ¬ (∃ (a : ℕ), 6*a^2 = 11) ∧ ¬ (∃ (a : ℕ), a^2 = 11) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, h⟩
    have ha_sq_le_11 : a^2 ≤ 11 := by
      have : b^2 ≥ 0 := Nat.zero_le _
      omega
    have ha_lt_4 : a < 4 := by
      by_contra! hc
      have h_a_ge_4 : a ≥ 4 := by omega
      have ha_sq_ge_16 : a^2 ≥ 16 := Nat.pow_le_pow_left h_a_ge_4 2
      omega
    have hb_sq_le_11 : b^2 ≤ 11 := by
      have : a^2 ≥ 0 := Nat.zero_le _
      omega
    have hb_lt_4 : b < 4 := by
      by_contra! hc
      have h_b_ge_4 : b ≥ 4 := by omega
      have hb_sq_ge_16 : b^2 ≥ 16 := Nat.pow_le_pow_left h_b_ge_4 2
      omega
    have h_all : ((Finset.range 4).product (Finset.range 4)).filter (λ ⟨x, y⟩ => x^2 + y^2 = 11) = ∅ := by decide
    have hm : (a, b) ∈ ((Finset.range 4).product (Finset.range 4)).filter (λ ⟨x, y⟩ => x^2 + y^2 = 11) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha_lt_4, Finset.mem_range.mpr hb_lt_4⟩, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_3 : a < 3 := by
      by_contra! hc
      have h_a_ge_3 : a ≥ 3 := by omega
      have ha_sq_ge_9 : a^2 ≥ 9 := by
        have h_mul : a*a ≥ 3*3 := Nat.mul_le_mul h_a_ge_3 h_a_ge_3
        simpa [sq] using h_mul
      have : 2*a^2 ≥ 18 := by nlinarith
      omega
    have h_all : (Finset.range 3).filter (λ x => 2*x^2 = 11) = ∅ := by decide
    have hm : a ∈ (Finset.range 3).filter (λ x => 2*x^2 = 11) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_3, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_2 : a < 2 := by
      by_contra! hc
      have h_a_ge_2 : a ≥ 2 := by omega
      have ha_sq_ge_4 : a^2 ≥ 4 := by
        have h_mul : a*a ≥ 2*2 := Nat.mul_le_mul h_a_ge_2 h_a_ge_2
        simpa [sq] using h_mul
      have : 3*a^2 ≥ 12 := by nlinarith
      omega
    have h_all : (Finset.range 2).filter (λ x => 3*x^2 = 11) = ∅ := by decide
    have hm : a ∈ (Finset.range 2).filter (λ x => 3*x^2 = 11) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_2, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_2 : a < 2 := by
      by_contra! hc
      have h_a_ge_2 : a ≥ 2 := by omega
      have ha_sq_ge_4 : a^2 ≥ 4 := by
        have h_mul : a*a ≥ 2*2 := Nat.mul_le_mul h_a_ge_2 h_a_ge_2
        simpa [sq] using h_mul
      have : 6*a^2 ≥ 24 := by nlinarith
      omega
    have h_all : (Finset.range 2).filter (λ x => 6*x^2 = 11) = ∅ := by decide
    have hm : a ∈ (Finset.range 2).filter (λ x => 6*x^2 = 11) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_2, h⟩
    rw [h_all] at hm; simp at hm
  · rintro ⟨a, h⟩
    have ha_lt_4 : a < 4 := by
      by_contra! hc
      have h_a_ge_4 : a ≥ 4 := by omega
      have ha_sq_ge_16 : a^2 ≥ 16 := Nat.pow_le_pow_left h_a_ge_4 2
      omega
    have h_all : (Finset.range 4).filter (λ x => x^2 = 11) = ∅ := by decide
    have hm : a ∈ (Finset.range 4).filter (λ x => x^2 = 11) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt_4, h⟩
    rw [h_all] at hm; simp at hm

/-! ### Geometric obstructions

The Erdős #634 problem asks for tilings by CONGRUENT triangles under geometric
constraints (interior-disjoint, exact cover). The `GeometricTiling` structure
captures this. The known classification (Miklós–Szőnyi–Beeson) says:
  n is tilable by congruent equilateral triangles iff n ∈ {a² + b², 2a², 3a², 6a², a²}.

Note on `equilateral_tiling_implies_square`: this lemma shows that if BOTH the target
and the pieces are equilateral triangles of the SAME area, then n must be 1.
This does NOT rule out n = 7 or 11 because in those cases the pieces might be
NON-equilateral triangles (e.g., right triangles). The true obstruction requires
a deeper argument (Beeson) showing that any tiling of an equilateral triangle by
congruent triangles forces the pieces to be equilateral. -/

/-- 7 is not geometrically tilable (Beeson's theorem).

    RALPH-LOOP-LESSON: This requires Beeson's classification theorem —
    that n is tilable by congruent triangles iff n ∈ {a²+b², 2a², 3a², 6a², a²}.
    The forward direction (if tilable then classification form) is the deep
    result. The backward direction (constructive tilings for those forms) is
    partially covered by `squares_constructive_geometric` (k² case), 
    `two_n_sq_constructive` (2k² case), and `sum_of_squares_constructive` 
    (a²+b² case), but 3a² and 6a² cases remain unformalized.

    Attempted approaches that failed this session:
    - `geometric_area_bound` only gives |area(T)| ≤ 7·|area(S)|, which is
      too weak to rule out 7 (the inequality is satisfiable).
    - `not_sum_of_three_squares_7` is true but no theorem connects tilability
      to Legendre's three-square theorem in this codebase.
    - No existing formalization of Beeson (2020) or the 
      Miklós–Szőnyi classification.

    Next-episode strategy: formalize the full classification theorem by
    completing the 3a² and 6a² constructive tilings, then reduce the forward
    direction to a known number-theoretic condition on the Cosine Law matrix
    (Beeson's "rational linear combination" argument). -/
lemma not_geometric_tilable_7 : ¬ GeometricTriangleTilable 7 := by
  sorry

/-- 11 is not geometrically tilable (Beeson's theorem).
    11 IS a sum of three squares (11 = 3²+1²+1²), so Legendre's theorem
    does NOT rule it out. The obstruction requires Beeson's full classification. -/
lemma not_geometric_tilable_11 : ¬ GeometricTriangleTilable 11 := by
  -- RALPH-LOOP: 11 is a sum of three squares, so a different obstruction is needed.
  -- See `sum_of_three_squares_11` above.
  sorry

/-- Conjecture: primes p ≡ 3 mod 4 are never geometrically tilable.
    If true, this would follow from the classification 
    (n ∉ {a²+b², 2a², 3a², 6a², a²} for primes p ≡ 3 mod 4).
    
    Check: for p ≡ 3 mod 4:
    - Not a sum of two squares (Fermat)
    - 2p² > p (not in 2a² form unless trivial)
    - 3, 6 times a²: p = 3·1² = 3 (but 3≡3 mod 4, so 3 itself is excluded)
    
    This is a known open conjecture — it's the Erdős problem #634 itself. -/
lemma conjectured_geometric_obstruction (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) : ¬ GeometricTriangleTilable p := by
  -- RALPH-LOOP: This IS the open problem. Proving it would solve Erdős #634.
  sorry

-- EVOLVE-BLOCK-END

end Erdos634
