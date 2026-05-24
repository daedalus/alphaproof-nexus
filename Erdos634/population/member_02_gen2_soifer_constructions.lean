import Mathlib

open Set Finset
open scoped Real

noncomputable section

/-
  Population Member 02: Strategy = Soifer's constructive families
  Approach: Formalize Soifer's constructions showing that n², 2n², 3n²,
    6n², and n²+m² are all tilable via geometric dissections of an
    equilateral triangle or right triangle.
  Rating (initial): Elo 1200
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

/-- Two triangles are congruent if their side lengths (squared) match pairwise. -/
def Congruent (T₁ T₂ : Triangle) : Prop :=
  (distSq T₁.A T₁.B = distSq T₂.A T₂.B ∧ distSq T₁.B T₁.C = distSq T₂.B T₂.C ∧ distSq T₁.C T₁.A = distSq T₂.C T₂.A) ∨
  (distSq T₁.A T₁.B = distSq T₂.B T₂.C ∧ distSq T₁.B T₁.C = distSq T₂.C T₂.A ∧ distSq T₁.C T₁.A = distSq T₂.A T₂.B) ∨
  (distSq T₁.A T₁.B = distSq T₂.C T₂.A ∧ distSq T₁.B T₁.C = distSq T₂.A T₂.B ∧ distSq T₁.C T₁.A = distSq T₂.B T₂.C)

/-- A tiling of a triangle T by n triangles each congruent to shape S.
    We construct pieces as an explicit Finset; area/cover constraints are
    stated as additional abstract premises we assume hold for each construction. -/
structure Tiling (T S : Triangle) (n : ℕ) where
  pieces : Finset Triangle
  card_eq : pieces.card = n
  all_congruent : ∀ t ∈ pieces, Congruent t S
  -- Additional constraints (disjointness, covering) omitted in this simplified model

/-- The property that there exists a triangle tileable by n congruent triangles. -/
def TriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (Tiling T S n)

-- EVOLVE-BLOCK-START

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
    Coordinates: (i/k + j/(2k), j*√3/(2k)) for i,j ≥ 0 with i+j ≤ k. -/
def lattice_point (i j k : ℕ) : ℝ × ℝ :=
  ((i : ℝ) / (k : ℝ) + (j : ℝ) / (2*(k : ℝ)), (j : ℝ) * Real.sqrt 3 / (2*(k : ℝ)))

/-- Upward triangle determinant: the shoelace formula gives √3/(2k²) when k > 0. -/
lemma up_triangle_det_eq (i j k : ℕ) (hk : k > 0) :
    (lattice_point i j k).1 * ((lattice_point (i+1) j k).2 - (lattice_point i (j+1) k).2) +
    (lattice_point (i+1) j k).1 * ((lattice_point i (j+1) k).2 - (lattice_point i j k).2) +
    (lattice_point i (j+1) k).1 * ((lattice_point i j k).2 - (lattice_point (i+1) j k).2) =
    Real.sqrt 3 / (2 * ((k : ℝ) ^ 2)) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  -- Expand lattice_point definitions
  simp [lattice_point]
  -- Now the goal is an equation in ℝ with Real.sqrt 3 as a factor.
  -- Factor out Real.sqrt 3 using ring, then use field_simp for the rational part.
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
    Vertices: bottom-left (i,j), bottom-right (i+1,j), top (i,j+1).
    Requires k > 0; for k=0 returns a dummy triangle (never used). -/
def up_triangle (i j k : ℕ) : Triangle :=
  if hk : k = 0 then
    { A := (0,0), B := (1,0), C := (0,1), nondegenerate := by norm_num }
  else
    { A := lattice_point i j k
      B := lattice_point (i+1) j k
      C := lattice_point i (j+1) k
      nondegenerate := by
        have hpos : k > 0 := Nat.pos_of_ne_zero hk
        have hpos' : (k : ℝ) ^ 2 > 0 := pow_pos (by exact_mod_cast hpos) 2
        have hnum : Real.sqrt 3 > 0 := by positivity
        have hcalc : (lattice_point i j k).1 * ((lattice_point (i+1) j k).2 - (lattice_point i (j+1) k).2) +
          (lattice_point (i+1) j k).1 * ((lattice_point i (j+1) k).2 - (lattice_point i j k).2) +
          (lattice_point i (j+1) k).1 * ((lattice_point i j k).2 - (lattice_point (i+1) j k).2) =
          Real.sqrt 3 / (2 * ((k : ℝ) ^ 2)) :=
          up_triangle_det_eq i j k hpos
        rw [hcalc]
        refine div_ne_zero (by positivity : Real.sqrt 3 ≠ 0) (by nlinarith) }

/-- A downward-pointing small equilateral triangle in the k×k grid (filling gaps).
    Vertices: top-left (i+1,j), top-right (i+1,j+1), bottom (i,j+1).
    Requires k > 0; for k=0 returns a dummy triangle (never used). -/
def down_triangle (i j k : ℕ) : Triangle :=
  if hk : k = 0 then
    { A := (0,0), B := (1,0), C := (0,1), nondegenerate := by norm_num }
  else
    { A := lattice_point (i+1) j k
      B := lattice_point (i+1) (j+1) k
      C := lattice_point i (j+1) k
      nondegenerate := by
        have hpos : k > 0 := Nat.pos_of_ne_zero hk
        have hpos' : (k : ℝ) ^ 2 > 0 := pow_pos (by exact_mod_cast hpos) 2
        have hnum : Real.sqrt 3 > 0 := by positivity
        have hcalc : (lattice_point (i+1) j k).1 * ((lattice_point (i+1) (j+1) k).2 - (lattice_point i (j+1) k).2) +
          (lattice_point (i+1) (j+1) k).1 * ((lattice_point i (j+1) k).2 - (lattice_point (i+1) j k).2) +
          (lattice_point i (j+1) k).1 * ((lattice_point (i+1) j k).2 - (lattice_point (i+1) (j+1) k).2) =
          Real.sqrt 3 / (2 * ((k : ℝ) ^ 2)) :=
          down_triangle_det_eq i j k hpos
        rw [hcalc]
        refine div_ne_zero (by positivity : Real.sqrt 3 ≠ 0) (by nlinarith) }

/-- All upward- and downward- pointing triangles for the k×k grid.
    Indices: 0 ≤ i,j < k with i+j < k for up, i+j < k-1 for down. -/
def grid_triangles (k : ℕ) : Finset Triangle :=
  (Finset.filter (λ ⟨i,j⟩ => i + j < k) (Finset.product (Finset.range k) (Finset.range k))).image (λ ⟨i,j⟩ => up_triangle i j k) ∪
  (Finset.filter (λ ⟨i,j⟩ => i + j < k - 1) (Finset.product (Finset.range (k-1)) (Finset.range (k-1)))).image (λ ⟨i,j⟩ => down_triangle i j k)

/-- The k×k grid of small equilateral triangles has exactly k² pieces.
    Count: k(k+1)/2 up triangles + k(k-1)/2 down triangles = k².
    When k=0, both sets are empty, card = 0 = 0².
    For k > 0, the images are disjoint (up/down triangles are at different positions),
    and each image is injective (different i,j give different triangles),
    so card = |{i+j<k}| + |{i+j<k-1}| where indices range over [0,k-1].
    The count ⍟(i+j < k for 0≤i,j<k) = k(k+1)/2, and ⍟(i+j < k-1 for 0≤i,j<k-1) = k(k-1)/2,
    sum = k².
    Combinatorial details deferred to keep the file focused on geometry. -/
lemma grid_card (k : ℕ) : (grid_triangles k).card = k^2 := by
  sorry

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

/-- The small triangle at the origin (up_triangle 0 0 k) is equilateral with side length 1/k.
    We show its three sides are equal. -/
lemma small_equilateral_sides (k : ℕ) (hk : k > 0) :
    distSq (up_triangle 0 0 k).A (up_triangle 0 0 k).B =
    distSq (up_triangle 0 0 k).B (up_triangle 0 0 k).C ∧
    distSq (up_triangle 0 0 k).B (up_triangle 0 0 k).C =
    distSq (up_triangle 0 0 k).C (up_triangle 0 0 k).A := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsq3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 3 from by norm_num)
  rcases distSq_up_triangle_eq 0 0 k hk with ⟨hAB, hBC, hCA⟩
  constructor
  · rw [hAB, hBC]
  · rw [hBC, hCA]

/-- Every triangle in the k×k grid is congruent to the small triangle (up_triangle 0 0 k).
    All triangles in the grid are equilateral with side length 1/k. -/
lemma grid_congruent (k : ℕ) (t : Triangle) (ht : t ∈ grid_triangles k) : Congruent t (up_triangle 0 0 k) := by
  by_cases hk0 : k = 0
  · -- When k=0, the grid is empty, so this case is impossible
    subst hk0
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

/-- Divide the equilateral triangle into k² smaller equilateral triangles
    via a grid of side length 1/k. Each small triangle is congruent to
    the small equilateral triangle at the origin (up_triangle 0 0 k). -/
lemma squares_constructive (k : ℕ) : TriangleTilable (k^2) := by
  refine ⟨equilateral, up_triangle 0 0 k, ?_⟩
  refine ⟨{
    pieces := grid_triangles k
    card_eq := grid_card k
    all_congruent := grid_congruent k
  }⟩

/-- 2k² construction (Soifer): take a right triangle and dissect into a k×k grid
    of 2k² congruent smaller right triangles.
    Method: subdivide the right triangle (0,0)-(1,0)-(0,√3) into k² copies of itself
    scaled by 1/k using parallel lines to both legs. Each small right triangle is
    further bisected by its altitude to produce 2 congruent right triangles,
    giving 2k² pieces total. The small triangles are congruent to right_triangle
    scaled by 1/k and rotated 90°. -/
lemma two_n_sq_constructive (k : ℕ) : TriangleTilable (2*k^2) := by
  refine ⟨right_triangle, right_triangle, ?_⟩
  -- Construction requires defining a Finset of 2k² right triangles and proving
  -- they are all congruent. This follows from the k×k grid dissection of the
  -- right triangle, where each cell is split along its diagonal.
  sorry

/-- 3k² construction (Soifer): divide an equilateral triangle into 3k² congruent
    30-60-90 right triangles.
    Method: draw lines from the center of the equilateral triangle to each vertex,
    partitioning into 3 congruent 120° sectors. Subdivide each sector into k²
    congruent 30-60-90 right triangles by drawing altitude lines. -/
lemma three_n_sq_constructive (k : ℕ) : TriangleTilable (3*k^2) := by
  refine ⟨equilateral, right_triangle, ?_⟩
  -- The small triangle shape is a 30-60-90 right triangle (half of equilateral).
  -- Each sector forms a kite shape subdivided into k² small triangles.
  sorry

/-- 6k² construction (Soifer): 6k² = 2·(3k²) = 3·(2k²).
    Soifer [So09c] constructs a right triangle with legs in ratio √3:√2 that
    admits tilings by both the 2k² pattern and the 3k² pattern simultaneously,
    giving a 6k² tiling by superposition.
    Full construction is documented in Soifer's book. -/
lemma six_n_sq_constructive (k : ℕ) : TriangleTilable (6*k^2) := by
  have h2 : TriangleTilable (2*k^2) := two_n_sq_constructive k
  have h3 : TriangleTilable (3*k^2) := three_n_sq_constructive k
  -- Soifer's construction: a right triangle with legs √3 and √2 can be tiled
  -- by both 2k² and 3k² patterns, giving 6k² via refinement.
  -- Not a simple product: requires a specific triangle shape that supports both
  -- dissections simultaneously.
  sorry

/-- n²+m² construction (Soifer): use a right triangle with legs proportional to n and m.
    Method: take a right triangle whose legs are in ratio n:m. Draw an n×m grid
    of lines parallel to the legs, creating 2·n·m small right triangles.
    However n²+m² ≠ 2nm in general. Soifer's construction uses a different right
    triangle where the hypotenuse can be decomposed into n²+m² segments via
    a Pythagorean decomposition.
    Reference: Soifer [So09c], Beeson's slides for details. -/
lemma sum_of_squares_constructive (a b : ℕ) : TriangleTilable (a^2 + b^2) := by
  sorry

-- EVOLVE-BLOCK-END

end Erdos634
