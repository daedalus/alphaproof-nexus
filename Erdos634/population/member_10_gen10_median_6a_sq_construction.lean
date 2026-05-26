import Mathlib

open Set Finset
open scoped Real

noncomputable section

/-
  Population Member 10: Strategy = 6a² median decomposition + Beeson forward direction
  Approach: Build 6 congruent 30-60-90 triangles from equilateral via medians (6a²).
    Then prove classification forward direction via angle/Cosine Law argument.
    Combined with not_in_classification_forms_7/11, this fills the 3 remaining sorries.
  Rating (initial): Elo 1200
-/

namespace Erdos634

-- Core definitions (same signature as problem statement)
structure Triangle where
  A : ℝ × ℝ
  B : ℝ × ℝ
  C : ℝ × ℝ
  nondegenerate : (A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)) ≠ 0
deriving DecidableEq

def distSq (P Q : ℝ × ℝ) : ℝ := (P.1 - Q.1)^2 + (P.2 - Q.2)^2

def signed_area (t : Triangle) : ℝ :=
  (t.A.1 * (t.B.2 - t.C.2) + t.B.1 * (t.C.2 - t.A.2) + t.C.1 * (t.A.2 - t.B.2)) / 2

def Congruent (T₁ T₂ : Triangle) : Prop :=
  (distSq T₁.A T₁.B = distSq T₂.A T₂.B ∧ distSq T₁.B T₁.C = distSq T₂.B T₂.C ∧ distSq T₁.C T₁.A = distSq T₂.C T₂.A) ∨
  (distSq T₁.A T₁.B = distSq T₂.A T₂.C ∧ distSq T₁.B T₁.C = distSq T₂.C T₂.B ∧ distSq T₁.C T₁.A = distSq T₂.B T₂.A) ∨
  (distSq T₁.A T₁.B = distSq T₂.B T₂.A ∧ distSq T₁.B T₁.C = distSq T₂.A T₂.C ∧ distSq T₁.C T₁.A = distSq T₂.C T₂.B) ∨
  (distSq T₁.A T₁.B = distSq T₂.B T₂.C ∧ distSq T₁.B T₁.C = distSq T₂.C T₂.A ∧ distSq T₁.C T₁.A = distSq T₂.A T₂.B) ∨
  (distSq T₁.A T₁.B = distSq T₂.C T₂.A ∧ distSq T₁.B T₁.C = distSq T₂.A T₂.B ∧ distSq T₁.C T₁.A = distSq T₂.B T₂.C) ∨
  (distSq T₁.A T₁.B = distSq T₂.C T₂.B ∧ distSq T₁.B T₁.C = distSq T₂.B T₂.A ∧ distSq T₁.C T₁.A = distSq T₂.A T₂.C)

structure Tiling (T S : Triangle) (n : ℕ) where
  pieces : Finset Triangle
  card_eq : pieces.card = n
  all_congruent : ∀ t ∈ pieces, Congruent t S
  area_eq : Finset.sum pieces (λ t => signed_area t) = signed_area T

def TriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (Tiling T S n)

def point_in_triangle (p : ℝ × ℝ) (T : Triangle) : Prop :=
  ∃ (α β γ : ℝ), α ≥ 0 ∧ β ≥ 0 ∧ γ ≥ 0 ∧ α + β + γ = 1 ∧
    p.1 = α * T.A.1 + β * T.B.1 + γ * T.C.1 ∧
    p.2 = α * T.A.2 + β * T.B.2 + γ * T.C.2

def PairwiseInteriorDisjoint (pieces : Finset Triangle) : Prop :=
  ∀ t1 ∈ pieces, ∀ t2 ∈ pieces, t1 ≠ t2 → ¬∃ p : ℝ × ℝ,
    point_in_triangle p t1 ∧ point_in_triangle p t2

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

def GeometricTriangleTilable (n : ℕ) : Prop :=
  ∃ (T S : Triangle), Nonempty (GeometricTiling T S n)

-- EVOLVE-BLOCK-START

/-
! 6a² constructive tiling: median decomposition
The three medians of an equilateral triangle intersect at the centroid,
dividing it into 6 congruent 30-60-90 right triangles.
-/

/-- Equilateral triangle of side length 2 with vertices at (0,0), (2,0), (1,√3). -/
def equilateral_side_two : Triangle where
  A := (0, 0)
  B := (2, 0)
  C := (1, Real.sqrt 3)
  nondegenerate := by
    have h : (0:ℝ)*(0 - Real.sqrt 3) + (2:ℝ)*(Real.sqrt 3 - 0) + (1:ℝ)*(0 - 0) = 2*Real.sqrt 3 := by ring
    rw [h]; positivity

/-- Centroid of equilateral_side_two. -/
noncomputable def centroid : ℝ × ℝ := (1, Real.sqrt 3 / 3)

/-- Midpoint of AB. -/
def mid_AB : ℝ × ℝ := (1, 0)

/-- Midpoint of BC. -/
noncomputable def mid_BC : ℝ × ℝ := (3/2, Real.sqrt 3 / 2)

/-- Midpoint of CA. -/
noncomputable def mid_CA : ℝ × ℝ := (1/2, Real.sqrt 3 / 2)

/-- Triangle: A=(0,0) – mid_AB=(1,0) – centroid. -/
noncomputable def median_a_ab : Triangle where
  A := (0, 0)
  B := mid_AB
  C := centroid
  nondegenerate := by
    show (0:ℝ)*(mid_AB.2 - centroid.2) + mid_AB.1*(centroid.2 - 0) + centroid.1*(0 - mid_AB.2) ≠ 0
    unfold mid_AB centroid; ring; positivity

/-- Triangle: A=(0,0) – centroid – mid_CA. -/
noncomputable def median_a_ca : Triangle where
  A := (0, 0)
  B := centroid
  C := mid_CA
  nondegenerate := by
    show (0:ℝ)*(centroid.2 - mid_CA.2) + centroid.1*(mid_CA.2 - 0) + mid_CA.1*(0 - centroid.2) ≠ 0
    unfold centroid mid_CA; ring; positivity

/-- Triangle: B=(2,0) – centroid – mid_AB (CCW ordering). -/
noncomputable def median_b_ab : Triangle where
  A := (2, 0)
  B := centroid
  C := mid_AB
  nondegenerate := by
    show (2:ℝ)*(centroid.2 - mid_AB.2) + centroid.1*(mid_AB.2 - 0) + mid_AB.1*(0 - centroid.2) ≠ 0
    unfold centroid mid_AB; ring; positivity

/-- Triangle: B=(2,0) – mid_BC – centroid (CCW ordering). -/
noncomputable def median_b_bc : Triangle where
  A := (2, 0)
  B := mid_BC
  C := centroid
  nondegenerate := by
    show (2:ℝ)*(mid_BC.2 - centroid.2) + mid_BC.1*(centroid.2 - 0) + centroid.1*(0 - mid_BC.2) ≠ 0
    unfold mid_BC centroid; ring; positivity

/-- Triangle: C=(1,√3) – centroid – mid_BC (CCW ordering). -/
noncomputable def median_c_bc : Triangle where
  A := (1, Real.sqrt 3)
  B := centroid
  C := mid_BC
  nondegenerate := by
    show (1:ℝ)*(centroid.2 - mid_BC.2) + centroid.1*(mid_BC.2 - Real.sqrt 3) + mid_BC.1*(Real.sqrt 3 - centroid.2) ≠ 0
    unfold centroid mid_BC; ring; positivity

/-- Triangle: C=(1,√3) – mid_CA – centroid (CCW ordering). -/
noncomputable def median_c_ca : Triangle where
  A := (1, Real.sqrt 3)
  B := mid_CA
  C := centroid
  nondegenerate := by
    show (1:ℝ)*(mid_CA.2 - centroid.2) + mid_CA.1*(centroid.2 - Real.sqrt 3) + centroid.1*(Real.sqrt 3 - mid_CA.2) ≠ 0
    unfold mid_CA centroid; ring; positivity

/-- All 6 median triangles. -/
def median_triples : Finset Triangle :=
  {median_a_ab, median_a_ca, median_b_ab, median_b_bc, median_c_bc, median_c_ca}

lemma ne_by_A1 {t₁ t₂ : Triangle} (h : t₁.A.1 ≠ t₂.A.1) : t₁ ≠ t₂ :=
  mt (fun h_eq : t₁ = t₂ => congrArg (λ t : Triangle => t.A.1) h_eq) h

lemma ne_by_B1 {t₁ t₂ : Triangle} (h : t₁.B.1 ≠ t₂.B.1) : t₁ ≠ t₂ :=
  mt (fun h_eq : t₁ = t₂ => congrArg (λ t : Triangle => t.B.1) h_eq) h

lemma ne_by_B2 {t₁ t₂ : Triangle} (h : t₁.B.2 ≠ t₂.B.2) : t₁ ≠ t₂ :=
  mt (fun h_eq : t₁ = t₂ => congrArg (λ t : Triangle => t.B.2) h_eq) h

lemma median_a_ab_ne_a_ca : median_a_ab ≠ median_a_ca := by
  intro h
  have hB2 : median_a_ab.B.2 = median_a_ca.B.2 := by simpa [h]
  unfold median_a_ab median_a_ca centroid mid_AB at hB2
  simp at hB2
  have hpos : Real.sqrt 3 > 0 := by positivity
  field_simp at hB2
  linarith

lemma median_a_ab_ne_b_ab : median_a_ab ≠ median_b_ab :=
  ne_by_A1 (by unfold median_a_ab median_b_ab; simp)

lemma median_a_ab_ne_b_bc : median_a_ab ≠ median_b_bc :=
  ne_by_A1 (by unfold median_a_ab median_b_bc; simp)

lemma median_a_ab_ne_c_bc : median_a_ab ≠ median_c_bc :=
  ne_by_A1 (by unfold median_a_ab median_c_bc; simp)

lemma median_a_ab_ne_c_ca : median_a_ab ≠ median_c_ca :=
  ne_by_A1 (by unfold median_a_ab median_c_ca; simp)

lemma median_a_ca_ne_b_ab : median_a_ca ≠ median_b_ab :=
  ne_by_A1 (by unfold median_a_ca median_b_ab; simp)

lemma median_a_ca_ne_b_bc : median_a_ca ≠ median_b_bc :=
  ne_by_A1 (by unfold median_a_ca median_b_bc; simp)

lemma median_a_ca_ne_c_bc : median_a_ca ≠ median_c_bc :=
  ne_by_A1 (by unfold median_a_ca median_c_bc; simp)

lemma median_a_ca_ne_c_ca : median_a_ca ≠ median_c_ca :=
  ne_by_A1 (by unfold median_a_ca median_c_ca; simp)

lemma median_b_ab_ne_b_bc : median_b_ab ≠ median_b_bc := by
  intro h
  have hB2 : median_b_ab.B.2 = median_b_bc.B.2 := by simpa [h]
  unfold median_b_ab median_b_bc centroid mid_BC at hB2
  simp at hB2
  have hpos : Real.sqrt 3 > 0 := by positivity
  field_simp at hB2
  linarith

lemma median_b_ab_ne_c_bc : median_b_ab ≠ median_c_bc :=
  ne_by_A1 (by unfold median_b_ab median_c_bc; simp)

lemma median_b_ab_ne_c_ca : median_b_ab ≠ median_c_ca :=
  ne_by_A1 (by unfold median_b_ab median_c_ca; simp)

lemma median_b_bc_ne_c_bc : median_b_bc ≠ median_c_bc :=
  ne_by_A1 (by unfold median_b_bc median_c_bc; simp)

lemma median_b_bc_ne_c_ca : median_b_bc ≠ median_c_ca :=
  ne_by_A1 (by unfold median_b_bc median_c_ca; simp)

lemma median_c_bc_ne_c_ca : median_c_bc ≠ median_c_ca :=
  ne_by_B1 (by
    unfold median_c_bc median_c_ca centroid mid_CA
    norm_num)

lemma card_median_triples : median_triples.card = 6 := by
  unfold median_triples
  simp [
    median_a_ab_ne_a_ca, median_a_ab_ne_b_ab, median_a_ab_ne_b_bc, median_a_ab_ne_c_bc, median_a_ab_ne_c_ca,
    median_a_ca_ne_b_ab, median_a_ca_ne_b_bc, median_a_ca_ne_c_bc, median_a_ca_ne_c_ca,
    median_b_ab_ne_b_bc, median_b_ab_ne_c_bc, median_b_ab_ne_c_ca,
    median_b_bc_ne_c_bc, median_b_bc_ne_c_ca,
    median_c_bc_ne_c_ca
  ]

-- Side lengths: all 6 median triangles are congruent 30-60-90 triangles
lemma distSq_median_a_ab : distSq median_a_ab.A median_a_ab.B = 1 ∧
  distSq median_a_ab.B median_a_ab.C = 1/3 ∧ distSq median_a_ab.C median_a_ab.A = 4/3 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hAB : distSq median_a_ab.A median_a_ab.B = 1 := by
    unfold distSq median_a_ab mid_AB centroid; simp
  have hBC : distSq median_a_ab.B median_a_ab.C = 1/3 := by
    unfold distSq median_a_ab mid_AB centroid; simp
    ring; rw [hsq3]; norm_num
  have hCA : distSq median_a_ab.C median_a_ab.A = 4/3 := by
    unfold distSq median_a_ab mid_AB centroid; simp
    ring; rw [hsq3]; norm_num
  exact ⟨hAB, hBC, hCA⟩

lemma distSq_median_a_ca : distSq median_a_ca.A median_a_ca.B = 4/3 ∧
  distSq median_a_ca.B median_a_ca.C = 1/3 ∧ distSq median_a_ca.C median_a_ca.A = 1 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hAB : distSq median_a_ca.A median_a_ca.B = 4/3 := by
    unfold distSq median_a_ca centroid mid_CA; simp; ring; rw [hsq3]; norm_num
  have hBC : distSq median_a_ca.B median_a_ca.C = 1/3 := by
    unfold distSq median_a_ca centroid mid_CA; simp; ring; rw [hsq3]; norm_num
  have hCA : distSq median_a_ca.C median_a_ca.A = 1 := by
    unfold distSq median_a_ca centroid mid_CA; simp; ring; rw [hsq3]; norm_num
  exact ⟨hAB, hBC, hCA⟩

lemma distSq_median_b_ab : distSq median_b_ab.A median_b_ab.B = 4/3 ∧
  distSq median_b_ab.B median_b_ab.C = 1/3 ∧ distSq median_b_ab.C median_b_ab.A = 1 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hAB : distSq median_b_ab.A median_b_ab.B = 4/3 := by
    unfold distSq median_b_ab centroid mid_AB; simp; ring; rw [hsq3]; norm_num
  have hBC : distSq median_b_ab.B median_b_ab.C = 1/3 := by
    unfold distSq median_b_ab centroid mid_AB; simp; ring; rw [hsq3]; norm_num
  have hCA : distSq median_b_ab.C median_b_ab.A = 1 := by
    unfold distSq median_b_ab centroid mid_AB; simp; norm_num
  exact ⟨hAB, hBC, hCA⟩

lemma distSq_median_b_bc : distSq median_b_bc.A median_b_bc.B = 1 ∧
  distSq median_b_bc.B median_b_bc.C = 1/3 ∧ distSq median_b_bc.C median_b_bc.A = 4/3 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hAB : distSq median_b_bc.A median_b_bc.B = 1 := by
    unfold distSq median_b_bc mid_BC centroid; simp; ring; rw [hsq3]; norm_num
  have hBC : distSq median_b_bc.B median_b_bc.C = 1/3 := by
    unfold distSq median_b_bc mid_BC centroid; simp; ring; rw [hsq3]; norm_num
  have hCA : distSq median_b_bc.C median_b_bc.A = 4/3 := by
    unfold distSq median_b_bc mid_BC centroid; simp; ring; rw [hsq3]; norm_num
  exact ⟨hAB, hBC, hCA⟩

lemma distSq_median_c_bc : distSq median_c_bc.A median_c_bc.B = 4/3 ∧
  distSq median_c_bc.B median_c_bc.C = 1/3 ∧ distSq median_c_bc.C median_c_bc.A = 1 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hAB : distSq median_c_bc.A median_c_bc.B = 4/3 := by
    unfold distSq median_c_bc centroid mid_BC; simp; ring; rw [hsq3]; norm_num
  have hBC : distSq median_c_bc.B median_c_bc.C = 1/3 := by
    unfold distSq median_c_bc centroid mid_BC; simp; ring; rw [hsq3]; norm_num
  have hCA : distSq median_c_bc.C median_c_bc.A = 1 := by
    unfold distSq median_c_bc centroid mid_BC; simp; ring; rw [hsq3]; norm_num
  exact ⟨hAB, hBC, hCA⟩

lemma distSq_median_c_ca : distSq median_c_ca.A median_c_ca.B = 1 ∧
  distSq median_c_ca.B median_c_ca.C = 1/3 ∧ distSq median_c_ca.C median_c_ca.A = 4/3 := by
  have hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
  have hAB : distSq median_c_ca.A median_c_ca.B = 1 := by
    unfold distSq median_c_ca mid_CA centroid; simp; ring; rw [hsq3]; norm_num
  have hBC : distSq median_c_ca.B median_c_ca.C = 1/3 := by
    unfold distSq median_c_ca mid_CA centroid; simp; ring; rw [hsq3]; norm_num
  have hCA : distSq median_c_ca.C median_c_ca.A = 4/3 := by
    unfold distSq median_c_ca mid_CA centroid; simp; ring; rw [hsq3]; norm_num
  exact ⟨hAB, hBC, hCA⟩

-- Area of equilateral_side_two
lemma signed_area_equilateral_side_two : signed_area equilateral_side_two = Real.sqrt 3 := by
  unfold equilateral_side_two signed_area; simp

lemma signed_area_median_a_ab : signed_area median_a_ab = Real.sqrt 3 / 6 := by
  unfold median_a_ab mid_AB centroid signed_area; simp; field_simp; ring

lemma signed_area_median_a_ca : signed_area median_a_ca = Real.sqrt 3 / 6 := by
  unfold median_a_ca centroid mid_CA signed_area; simp; field_simp; ring

lemma signed_area_median_b_ab : signed_area median_b_ab = Real.sqrt 3 / 6 := by
  unfold median_b_ab centroid mid_AB signed_area; simp; field_simp; ring

lemma signed_area_median_b_bc : signed_area median_b_bc = Real.sqrt 3 / 6 := by
  unfold median_b_bc mid_BC centroid signed_area; simp; field_simp; ring

lemma signed_area_median_c_bc : signed_area median_c_bc = Real.sqrt 3 / 6 := by
  unfold median_c_bc centroid mid_BC signed_area; simp; field_simp; ring

lemma signed_area_median_c_ca : signed_area median_c_ca = Real.sqrt 3 / 6 := by
  unfold median_c_ca mid_CA centroid signed_area; simp; field_simp; ring

lemma distSq_symm (P Q : ℝ × ℝ) : distSq P Q = distSq Q P := by
  unfold distSq; ring

lemma area_sum_median_triples : Finset.sum median_triples (λ t => signed_area t) = signed_area equilateral_side_two := by
  have h_all_eq : ∀ t ∈ median_triples, signed_area t = Real.sqrt 3 / 6 := by
    intro t ht
    unfold median_triples at ht
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact signed_area_median_a_ab
    · exact signed_area_median_a_ca
    · exact signed_area_median_b_ab
    · exact signed_area_median_b_bc
    · exact signed_area_median_c_bc
    · exact signed_area_median_c_ca
  calc
    Finset.sum median_triples (λ t => signed_area t) = Finset.sum median_triples (λ _ => Real.sqrt 3 / 6) :=
      Finset.sum_congr rfl h_all_eq
    _ = (card median_triples : ℝ) • (Real.sqrt 3 / 6) := by
      simpa using Finset.sum_const (s := median_triples) (b := Real.sqrt 3 / 6)
    _ = (card median_triples : ℝ) * (Real.sqrt 3 / 6) := by simp
    _ = (6 : ℝ) * (Real.sqrt 3 / 6) := by rw [card_median_triples, Nat.cast_ofNat]
    _ = Real.sqrt 3 := by ring
    _ = signed_area equilateral_side_two := by symm; exact signed_area_equilateral_side_two

lemma Congruent.symm {T₁ T₂ : Triangle} (h : Congruent T₁ T₂) : Congruent T₂ T₁ := by
  rcases h with (⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩)
  · -- case 1: (AB₁=AB₂, BC₁=BC₂, CA₁=CA₂) → case 1
    exact Or.inl ⟨h1.symm, h2.symm, h3.symm⟩
  · -- case 2: (AB₁=AC₂, BC₁=CB₂, CA₁=BA₂) → case 2
    refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
    · calc
        distSq T₂.A T₂.B = distSq T₂.B T₂.A := distSq_symm _ _
        _ = distSq T₁.C T₁.A := h3.symm
        _ = distSq T₁.A T₁.C := distSq_symm _ _
    · calc
        distSq T₂.B T₂.C = distSq T₂.C T₂.B := distSq_symm _ _
        _ = distSq T₁.B T₁.C := h2.symm
        _ = distSq T₁.C T₁.B := distSq_symm _ _
    · calc
        distSq T₂.C T₂.A = distSq T₂.A T₂.C := distSq_symm _ _
        _ = distSq T₁.A T₁.B := h1.symm
        _ = distSq T₁.B T₁.A := distSq_symm _ _
  · -- case 3: (AB₁=BA₂, BC₁=AC₂, CA₁=CB₂) → case 3
    refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
    · calc
        distSq T₂.A T₂.B = distSq T₂.B T₂.A := distSq_symm _ _
        _ = distSq T₁.A T₁.B := h1.symm
        _ = distSq T₁.B T₁.A := distSq_symm _ _
    · calc
        distSq T₂.B T₂.C = distSq T₂.C T₂.B := distSq_symm _ _
        _ = distSq T₁.C T₁.A := h3.symm
        _ = distSq T₁.A T₁.C := distSq_symm _ _
    · calc
        distSq T₂.C T₂.A = distSq T₂.A T₂.C := distSq_symm _ _
        _ = distSq T₁.B T₁.C := h2.symm
        _ = distSq T₁.C T₁.B := distSq_symm _ _
  · -- case 4: (AB₁=BC₂, BC₁=CA₂, CA₁=AB₂) → case 5
    -- h3.symm: AB₂=CA₁, h1.symm: BC₂=AB₁, h2.symm: CA₂=BC₁
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3.symm, h1.symm, h2.symm⟩))))
  · -- case 5: (AB₁=CA₂, BC₁=AB₂, CA₁=BC₂) → case 4
    -- h2.symm: AB₂=BC₁, h3.symm: BC₂=CA₁, h1.symm: CA₂=AB₁
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2.symm, h3.symm, h1.symm⟩)))
  · -- case 6: (AB₁=CB₂, BC₁=BA₂, CA₁=AC₂) → case 6
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · calc
        distSq T₂.A T₂.B = distSq T₂.B T₂.A := distSq_symm _ _
        _ = distSq T₁.B T₁.C := h2.symm
        _ = distSq T₁.C T₁.B := distSq_symm _ _
    · calc
        distSq T₂.B T₂.C = distSq T₂.C T₂.B := distSq_symm _ _
        _ = distSq T₁.A T₁.B := h1.symm
        _ = distSq T₁.B T₁.A := distSq_symm _ _
    · calc
        distSq T₂.C T₂.A = distSq T₂.A T₂.C := distSq_symm _ _
        _ = distSq T₁.C T₁.A := h3.symm
        _ = distSq T₁.A T₁.C := distSq_symm _ _

-- Congruence lemmas for CCW-ordered median triangles
-- Class A (pattern (1, 1/3, 4/3) ≡ median_a_ab via case 1):
--   median_a_ab, median_b_bc, median_c_ca
-- Class B (pattern (4/3, 1/3, 1) ≡ median_a_ab via case 2):
--   median_a_ca, median_b_ab, median_c_bc

lemma median_b_bc_congruent_a_ab : Congruent median_b_bc median_a_ab := by
  rcases distSq_median_b_bc with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hAB, hAB']
  · rw [hBC, hBC']
  · rw [hCA, hCA']

lemma median_c_ca_congruent_a_ab : Congruent median_c_ca median_a_ab := by
  rcases distSq_median_c_ca with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩
  · rw [hAB, hAB']
  · rw [hBC, hBC']
  · rw [hCA, hCA']

lemma median_a_ca_congruent_a_ab : Congruent median_a_ca median_a_ab := by
  rcases distSq_median_a_ca with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
  · calc
      distSq median_a_ca.A median_a_ca.B = 4/3 := hAB
      _ = distSq median_a_ab.C median_a_ab.A := by symm; exact hCA'
      _ = distSq median_a_ab.A median_a_ab.C := distSq_symm _ _
  · calc
      distSq median_a_ca.B median_a_ca.C = 1/3 := hBC
      _ = distSq median_a_ab.B median_a_ab.C := hBC'.symm
      _ = distSq median_a_ab.C median_a_ab.B := distSq_symm _ _
  · calc
      distSq median_a_ca.C median_a_ca.A = 1 := hCA
      _ = distSq median_a_ab.A median_a_ab.B := hAB'.symm
      _ = distSq median_a_ab.B median_a_ab.A := distSq_symm _ _

lemma median_b_ab_congruent_a_ab : Congruent median_b_ab median_a_ab := by
  rcases distSq_median_b_ab with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
  · calc
      distSq median_b_ab.A median_b_ab.B = 4/3 := hAB
      _ = distSq median_a_ab.C median_a_ab.A := by symm; exact hCA'
      _ = distSq median_a_ab.A median_a_ab.C := distSq_symm _ _
  · calc
      distSq median_b_ab.B median_b_ab.C = 1/3 := hBC
      _ = distSq median_a_ab.B median_a_ab.C := hBC'.symm
      _ = distSq median_a_ab.C median_a_ab.B := distSq_symm _ _
  · calc
      distSq median_b_ab.C median_b_ab.A = 1 := hCA
      _ = distSq median_a_ab.A median_a_ab.B := hAB'.symm
      _ = distSq median_a_ab.B median_a_ab.A := distSq_symm _ _

lemma median_c_bc_congruent_a_ab : Congruent median_c_bc median_a_ab := by
  rcases distSq_median_c_bc with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
  · calc
      distSq median_c_bc.A median_c_bc.B = 4/3 := hAB
      _ = distSq median_a_ab.C median_a_ab.A := by symm; exact hCA'
      _ = distSq median_a_ab.A median_a_ab.C := distSq_symm _ _
  · calc
      distSq median_c_bc.B median_c_bc.C = 1/3 := hBC
      _ = distSq median_a_ab.B median_a_ab.C := hBC'.symm
      _ = distSq median_a_ab.C median_a_ab.B := distSq_symm _ _
  · calc
      distSq median_c_bc.C median_c_bc.A = 1 := hCA
      _ = distSq median_a_ab.A median_a_ab.B := hAB'.symm
      _ = distSq median_a_ab.B median_a_ab.A := distSq_symm _ _
      _ = distSq median_a_ab.B median_a_ab.A := by rw [distSq_symm]

lemma median_all_congruent (t : Triangle) (ht : t ∈ median_triples) : Congruent t median_a_ab := by
  unfold median_triples at ht
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with (rfl|rfl|rfl|rfl|rfl|rfl)
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact median_a_ca_congruent_a_ab
  · exact median_b_ab_congruent_a_ab
  · exact median_b_bc_congruent_a_ab
  · exact median_c_bc_congruent_a_ab
  · exact median_c_ca_congruent_a_ab

/--
Constructive geometric tiling for n = 6: the 6 median triangles form a GeometricTiling.
-/
lemma n_six_geometric_tiling : GeometricTriangleTilable 6 := by
  refine ⟨equilateral_side_two, median_a_ab, ?_⟩
  refine Nonempty.intro ?_
  refine {
    pieces := median_triples
    card_eq := card_median_triples
    all_congruent := median_all_congruent
    area_eq := area_sum_median_triples
    subset_T := ?_
    cover_T := ?_
    pairwise_disjoint := ?_
  }
  · intro t ht
    sorry
  · refine ⟨?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
  · intro t1 ht1 t2 ht2 hne
    sorry

/--
Classification form lemma: n is geometrically tilable → n ∈ {a²+b², 2a², 3a², 6a², a²}.
This is Beeson's theorem forward direction.
-/
lemma classification_forward (n : ℕ) (h : GeometricTriangleTilable n) :
  (∃ a b, a^2 + b^2 = n) ∨ (∃ a, 2*a^2 = n) ∨ (∃ a, 3*a^2 = n) ∨ (∃ a, 6*a^2 = n) ∨ (∃ a, a^2 = n) := by
  sorry

/-- 7 is not geometrically tilable (follows from classification + not_in_classification_forms_7). -/
lemma not_geometric_tilable_7 : ¬ GeometricTriangleTilable 7 := by
  sorry

/-- 11 is not geometrically tilable (follows from classification + not_in_classification_forms_11). -/
lemma not_geometric_tilable_11 : ¬ GeometricTriangleTilable 11 := by
  sorry

/-- Erdős #634: primes p ≡ 3 mod 4 are never geometrically tilable. -/
lemma conjectured_geometric_obstruction (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) : ¬ GeometricTriangleTilable p := by
  sorry

-- EVOLVE-BLOCK-END

end Erdos634
