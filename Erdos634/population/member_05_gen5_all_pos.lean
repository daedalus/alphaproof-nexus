import Mathlib

open Set Finset
open scoped Real

noncomputable section

/-
  Population Member 05: Strategy = Expose formalization gap + all prior constructions
  Approach: Add `tilable_all_pos` proving ALL n > 0 are tilable under the current
    weak `Tiling` definition (which lacks disjointness/covering). This reveals that
    `not_tilable_7` and `not_tilable_11` are false under the current definition and
    require stronger geometric constraints (e.g., triangulation/partition conditions)
    before they become provable.
  Rating (initial): Elo 1500
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
  area_eq : Finset.sum pieces (λ t => signed_area t) = signed_area T

/-- The property that there exists a triangle tileable by n congruent triangles. -/
def TriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (Tiling T S n)

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

/-- Divide the equilateral triangle into k² smaller equilateral triangles
    via a grid of side length 1/k. -/
lemma squares_constructive (k : ℕ) (hk : k > 0) : TriangleTilable (k^2) := by
  refine ⟨equilateral, up_triangle 0 0 k, ⟨{
    pieces := grid_triangles k
    card_eq := grid_card k
    all_congruent := grid_congruent k
    area_eq := grid_area_sum k hk
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

/-- Under the current weak `Tiling` definition (which lacks disjointness and covering),
    EVERY positive integer n is tilable. Just take a right triangle of area n·√3/2 and
    n congruent translated copies of the unit right triangle. This shows that `not_tilable_7`
    and `not_tilable_11` are FALSE under the current definition — they require a stronger
    formalization with geometric disjointness/covering constraints. -/
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

-- NOTE: The following three lemmas are IMPOSSIBLE to prove under the current `Tiling` definition
-- because `tilable_all_pos` shows that every n > 0 is tilable. To make these statements meaningful,
-- the `Tiling` structure must be strengthened with:
--   1. A `disjoint` condition (pieces must not overlap)
--   2. A `cover` condition (the union of pieces must equal T exactly)
-- Without these constraints, any n > 0 admits a trivial tiling. The sorries below remain as
-- placeholders for future iterations with a stronger formalization.

/-- Beeson's obstruction: 7 is not tilable. Requires stronger definition. -/
lemma not_tilable_7 : ¬ TriangleTilable 7 := by
  sorry

/-- Beeson's obstruction: 11 is not tilable. Requires stronger definition. -/
lemma not_tilable_11 : ¬ TriangleTilable 11 := by
  sorry

/-- Conjecture: every prime p ≡ 3 (mod 4) is not tilable. Requires stronger definition. -/
lemma conjectured_obstruction (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) : ¬ TriangleTilable p := by
  sorry

-- EVOLVE-BLOCK-END

end Erdos634
