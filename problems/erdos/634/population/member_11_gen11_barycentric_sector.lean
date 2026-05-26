import Mathlib

open Set Finset
open scoped Real

noncomputable section

/-
  Population Member 11: Strategy = Barycentric sector decomposition for n=6 median tiling
  Approach: Define barycentric functions (ba,bb,bc) for equilateral triangle E of side 2.
    Show 6 median triangles correspond to the 6 strict total orders of (ba,bb,bc)
    for interior points. This gives pairwise disjointness via ordering incompatibility.
  Rating (initial): Elo 1200
-/

namespace Erdos634

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
  ∃ (u v w : ℝ), u ≥ 0 ∧ v ≥ 0 ∧ w ≥ 0 ∧ u + v + w = 1 ∧
    p.1 = u * T.A.1 + v * T.B.1 + w * T.C.1 ∧
    p.2 = u * T.A.2 + v * T.B.2 + w * T.C.2

def point_in_interior (p : ℝ × ℝ) (T : Triangle) : Prop :=
  ∃ (u v w : ℝ), u > 0 ∧ v > 0 ∧ w > 0 ∧ u + v + w = 1 ∧
    p.1 = u * T.A.1 + v * T.B.1 + w * T.C.1 ∧
    p.2 = u * T.A.2 + v * T.B.2 + w * T.C.2

def PairwiseInteriorDisjoint (pieces : Finset Triangle) : Prop :=
  ∀ t1 ∈ pieces, ∀ t2 ∈ pieces, t1 ≠ t2 → ¬∃ p : ℝ × ℝ,
    point_in_interior p t1 ∧ point_in_interior p t2

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

/- Equilateral triangle E: vertices A=(0,0), B=(2,0), C=(1,√3), area = √3 -/

def equilateral_side_two : Triangle where
  A := (0, 0)
  B := (2, 0)
  C := (1, Real.sqrt 3)
  nondegenerate := by
    have h : (0:ℝ)*(0 - Real.sqrt 3) + (2:ℝ)*(Real.sqrt 3 - 0) + (1:ℝ)*(0 - 0) = 2*Real.sqrt 3 := by ring
    rw [h]; positivity

/-- Barycentric coordinates of p w.r.t. equilateral_side_two. -/
noncomputable def ba (p : ℝ × ℝ) : ℝ := 1 - p.1/2 - p.2/(2*Real.sqrt 3)
noncomputable def bb (p : ℝ × ℝ) : ℝ := p.1/2 - p.2/(2*Real.sqrt 3)
noncomputable def bc (p : ℝ × ℝ) : ℝ := p.2/Real.sqrt 3

lemma ba_bb_bc_sum (p : ℝ × ℝ) : ba p + bb p + bc p = 1 := by
  dsimp [ba, bb, bc]; ring

lemma h_sq3_ne : Real.sqrt 3 ≠ 0 := by positivity

lemma mem_equilateral_iff (p : ℝ × ℝ) : point_in_triangle p equilateral_side_two ↔ ba p ≥ 0 ∧ bb p ≥ 0 ∧ bc p ≥ 0 := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, hsum, hx, hy⟩
    have hba_eq : ba p = u := by
      calc
        ba p = 1 - (2*v + w)/2 - (Real.sqrt 3 * w)/(2*Real.sqrt 3) := by
          dsimp [ba]; rw [hx, hy]; dsimp [equilateral_side_two]
          field_simp [h_sq3_ne]; ring
        _ = 1 - v - w := by
          field_simp [h_sq3_ne]; ring
        _ = u := by nlinarith
    have hbb_eq : bb p = v := by
      calc
        bb p = (2*v + w)/2 - (Real.sqrt 3 * w)/(2*Real.sqrt 3) := by
          dsimp [bb]; rw [hx, hy]; dsimp [equilateral_side_two]
          field_simp [h_sq3_ne]; ring
        _ = v := by
          field_simp [h_sq3_ne]; ring
    have hbc_eq : bc p = w := by
      calc
        bc p = (Real.sqrt 3 * w)/Real.sqrt 3 := by
          dsimp [bc]; rw [hy]; dsimp [equilateral_side_two]
          field_simp [h_sq3_ne]; ring
        _ = w := by
          field_simp [h_sq3_ne]
    have hba : ba p ≥ 0 := by rw [hba_eq]; exact hu
    have hbb : bb p ≥ 0 := by rw [hbb_eq]; exact hv
    have hbc : bc p ≥ 0 := by rw [hbc_eq]; exact hw
    exact ⟨hba, hbb, hbc⟩
  · rintro ⟨hba, hbb, hbc⟩
    refine ⟨ba p, bb p, bc p, hba, hbb, hbc, ba_bb_bc_sum p, ?_, ?_⟩
    · dsimp [ba, bb, bc, equilateral_side_two]; field_simp [h_sq3_ne]; ring
    · dsimp [ba, bb, bc, equilateral_side_two]; field_simp [h_sq3_ne]; ring

/- The 6 median triangles -/

noncomputable def centroid : ℝ × ℝ := (1, Real.sqrt 3 / 3)
def mid_AB : ℝ × ℝ := (1, 0)
noncomputable def mid_BC : ℝ × ℝ := (3/2, Real.sqrt 3 / 2)
noncomputable def mid_CA : ℝ × ℝ := (1/2, Real.sqrt 3 / 2)

noncomputable def median_a_ab : Triangle where
  A := (0, 0); B := mid_AB; C := centroid
  nondegenerate := by unfold mid_AB centroid; ring; positivity

noncomputable def median_a_ca : Triangle where
  A := (0, 0); B := centroid; C := mid_CA
  nondegenerate := by unfold centroid mid_CA; ring; positivity

noncomputable def median_b_ab : Triangle where
  A := (2, 0); B := centroid; C := mid_AB
  nondegenerate := by unfold centroid mid_AB; ring; positivity

noncomputable def median_b_bc : Triangle where
  A := (2, 0); B := mid_BC; C := centroid
  nondegenerate := by unfold mid_BC centroid; ring; positivity

noncomputable def median_c_bc : Triangle where
  A := (1, Real.sqrt 3); B := centroid; C := mid_BC
  nondegenerate := by unfold centroid mid_BC; ring; positivity

noncomputable def median_c_ca : Triangle where
  A := (1, Real.sqrt 3); B := mid_CA; C := centroid
  nondegenerate := by unfold mid_CA centroid; ring; positivity

def median_triples : Finset Triangle :=
  {median_a_ab, median_a_ca, median_b_ab, median_b_bc, median_c_bc, median_c_ca}

lemma ne_by_A1 {t₁ t₂ : Triangle} (h : t₁.A.1 ≠ t₂.A.1) : t₁ ≠ t₂ :=
  mt (fun h_eq : t₁ = t₂ => congrArg (λ t : Triangle => t.A.1) h_eq) h

lemma ne_by_B1 {t₁ t₂ : Triangle} (h : t₁.B.1 ≠ t₂.B.1) : t₁ ≠ t₂ :=
  mt (fun h_eq : t₁ = t₂ => congrArg (λ t : Triangle => t.B.1) h_eq) h

lemma median_a_ab_ne_a_ca : median_a_ab ≠ median_a_ca := by
  intro h; have hB2 : median_a_ab.B.2 = median_a_ca.B.2 := by simpa [h]
  unfold median_a_ab median_a_ca centroid mid_AB at hB2; simp at hB2
  have hpos : Real.sqrt 3 > 0 := by positivity
  linarith

lemma median_a_ab_ne_b_ab : median_a_ab ≠ median_b_ab := ne_by_A1 (by unfold median_a_ab median_b_ab; simp)
lemma median_a_ab_ne_b_bc : median_a_ab ≠ median_b_bc := ne_by_A1 (by unfold median_a_ab median_b_bc; simp)
lemma median_a_ab_ne_c_bc : median_a_ab ≠ median_c_bc := ne_by_A1 (by unfold median_a_ab median_c_bc; simp)
lemma median_a_ab_ne_c_ca : median_a_ab ≠ median_c_ca := ne_by_A1 (by unfold median_a_ab median_c_ca; simp)
lemma median_a_ca_ne_b_ab : median_a_ca ≠ median_b_ab := ne_by_A1 (by unfold median_a_ca median_b_ab; simp)
lemma median_a_ca_ne_b_bc : median_a_ca ≠ median_b_bc := ne_by_A1 (by unfold median_a_ca median_b_bc; simp)
lemma median_a_ca_ne_c_bc : median_a_ca ≠ median_c_bc := ne_by_A1 (by unfold median_a_ca median_c_bc; simp)
lemma median_a_ca_ne_c_ca : median_a_ca ≠ median_c_ca := ne_by_A1 (by unfold median_a_ca median_c_ca; simp)

lemma median_b_ab_ne_b_bc : median_b_ab ≠ median_b_bc := by
  intro h; have hB2 : median_b_ab.B.2 = median_b_bc.B.2 := by simpa [h]
  unfold median_b_ab median_b_bc centroid mid_BC at hB2; simp at hB2
  field_simp [h_sq3_ne] at hB2; norm_num at hB2

lemma median_b_ab_ne_c_bc : median_b_ab ≠ median_c_bc := ne_by_A1 (by unfold median_b_ab median_c_bc; simp)
lemma median_b_ab_ne_c_ca : median_b_ab ≠ median_c_ca := ne_by_A1 (by unfold median_b_ab median_c_ca; simp)
lemma median_b_bc_ne_c_bc : median_b_bc ≠ median_c_bc := ne_by_A1 (by unfold median_b_bc median_c_bc; simp)
lemma median_b_bc_ne_c_ca : median_b_bc ≠ median_c_ca := ne_by_A1 (by unfold median_b_bc median_c_ca; simp)
lemma median_c_bc_ne_c_ca : median_c_bc ≠ median_c_ca := ne_by_B1 (by unfold median_c_bc median_c_ca centroid mid_CA; norm_num)

lemma card_median_triples : median_triples.card = 6 := by
  unfold median_triples
  simp [median_a_ab_ne_a_ca, median_a_ab_ne_b_ab, median_a_ab_ne_b_bc, median_a_ab_ne_c_bc, median_a_ab_ne_c_ca,
    median_a_ca_ne_b_ab, median_a_ca_ne_b_bc, median_a_ca_ne_c_bc, median_a_ca_ne_c_ca,
    median_b_ab_ne_b_bc, median_b_ab_ne_c_bc, median_b_ab_ne_c_ca,
    median_b_bc_ne_c_bc, median_b_bc_ne_c_ca, median_c_bc_ne_c_ca]

/- Side lengths and area -/

lemma hsq3 : (Real.sqrt 3)^2 = (3 : ℝ) := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))

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

/- Congruence lemmas -/

lemma distSq_symm (P Q : ℝ × ℝ) : distSq P Q = distSq Q P := by
  unfold distSq; ring

lemma distSq_median_a_ab : distSq median_a_ab.A median_a_ab.B = 1 ∧
  distSq median_a_ab.B median_a_ab.C = 1/3 ∧ distSq median_a_ab.C median_a_ab.A = 4/3 := by
  have hAB : distSq median_a_ab.A median_a_ab.B = 1 := by
    unfold distSq median_a_ab mid_AB centroid; simp
  have hBC : distSq median_a_ab.B median_a_ab.C = 1/3 := by
    unfold distSq median_a_ab mid_AB centroid; simp; ring; rw [hsq3]; norm_num
  have hCA : distSq median_a_ab.C median_a_ab.A = 4/3 := by
    unfold distSq median_a_ab mid_AB centroid; simp; ring; rw [hsq3]; norm_num
  exact ⟨hAB, hBC, hCA⟩

lemma distSq_median_a_ca : distSq median_a_ca.A median_a_ca.B = 4/3 ∧
  distSq median_a_ca.B median_a_ca.C = 1/3 ∧ distSq median_a_ca.C median_a_ca.A = 1 := by
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

lemma Congruent.symm {T₁ T₂ : Triangle} (h : Congruent T₁ T₂) : Congruent T₂ T₁ := by
  rcases h with (⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩|⟨h1, h2, h3⟩)
  · exact Or.inl ⟨h1.symm, h2.symm, h3.symm⟩
  · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
    · calc distSq T₂.A T₂.B = distSq T₂.B T₂.A := distSq_symm _ _
      _ = distSq T₁.C T₁.A := h3.symm
      _ = distSq T₁.A T₁.C := distSq_symm _ _
    · calc distSq T₂.B T₂.C = distSq T₂.C T₂.B := distSq_symm _ _
      _ = distSq T₁.B T₁.C := h2.symm
      _ = distSq T₁.C T₁.B := distSq_symm _ _
    · calc distSq T₂.C T₂.A = distSq T₂.A T₂.C := distSq_symm _ _
      _ = distSq T₁.A T₁.B := h1.symm
      _ = distSq T₁.B T₁.A := distSq_symm _ _
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
    · calc distSq T₂.A T₂.B = distSq T₂.B T₂.A := distSq_symm _ _
      _ = distSq T₁.A T₁.B := h1.symm
      _ = distSq T₁.B T₁.A := distSq_symm _ _
    · calc distSq T₂.B T₂.C = distSq T₂.C T₂.B := distSq_symm _ _
      _ = distSq T₁.C T₁.A := h3.symm
      _ = distSq T₁.A T₁.C := distSq_symm _ _
    · calc distSq T₂.C T₂.A = distSq T₂.A T₂.C := distSq_symm _ _
      _ = distSq T₁.B T₁.C := h2.symm
      _ = distSq T₁.C T₁.B := distSq_symm _ _
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3.symm, h1.symm, h2.symm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2.symm, h3.symm, h1.symm⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))))
    · calc distSq T₂.A T₂.B = distSq T₂.B T₂.A := distSq_symm _ _
      _ = distSq T₁.B T₁.C := h2.symm
      _ = distSq T₁.C T₁.B := distSq_symm _ _
    · calc distSq T₂.B T₂.C = distSq T₂.C T₂.B := distSq_symm _ _
      _ = distSq T₁.A T₁.B := h1.symm
      _ = distSq T₁.B T₁.A := distSq_symm _ _
    · calc distSq T₂.C T₂.A = distSq T₂.A T₂.C := distSq_symm _ _
      _ = distSq T₁.C T₁.A := h3.symm
      _ = distSq T₁.A T₁.C := distSq_symm _ _

lemma median_b_bc_congruent_a_ab : Congruent median_b_bc median_a_ab := by
  rcases distSq_median_b_bc with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩; rw [hAB, hAB']; rw [hBC, hBC']; rw [hCA, hCA']

lemma median_c_ca_congruent_a_ab : Congruent median_c_ca median_a_ab := by
  rcases distSq_median_c_ca with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inl ⟨?_, ?_, ?_⟩; rw [hAB, hAB']; rw [hBC, hBC']; rw [hCA, hCA']

lemma median_a_ca_congruent_a_ab : Congruent median_a_ca median_a_ab := by
  rcases distSq_median_a_ca with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
  · calc distSq median_a_ca.A median_a_ca.B = 4/3 := hAB
      _ = distSq median_a_ab.C median_a_ab.A := by symm; exact hCA'
      _ = distSq median_a_ab.A median_a_ab.C := distSq_symm _ _
  · calc distSq median_a_ca.B median_a_ca.C = 1/3 := hBC
      _ = distSq median_a_ab.B median_a_ab.C := hBC'.symm
      _ = distSq median_a_ab.C median_a_ab.B := distSq_symm _ _
  · calc distSq median_a_ca.C median_a_ca.A = 1 := hCA
      _ = distSq median_a_ab.A median_a_ab.B := hAB'.symm
      _ = distSq median_a_ab.B median_a_ab.A := distSq_symm _ _

lemma median_b_ab_congruent_a_ab : Congruent median_b_ab median_a_ab := by
  rcases distSq_median_b_ab with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
  · calc distSq median_b_ab.A median_b_ab.B = 4/3 := hAB
      _ = distSq median_a_ab.C median_a_ab.A := by symm; exact hCA'
      _ = distSq median_a_ab.A median_a_ab.C := distSq_symm _ _
  · calc distSq median_b_ab.B median_b_ab.C = 1/3 := hBC
      _ = distSq median_a_ab.B median_a_ab.C := hBC'.symm
      _ = distSq median_a_ab.C median_a_ab.B := distSq_symm _ _
  · calc distSq median_b_ab.C median_b_ab.A = 1 := hCA
      _ = distSq median_a_ab.A median_a_ab.B := hAB'.symm
      _ = distSq median_a_ab.B median_a_ab.A := distSq_symm _ _

lemma median_c_bc_congruent_a_ab : Congruent median_c_bc median_a_ab := by
  rcases distSq_median_c_bc with ⟨hAB, hBC, hCA⟩
  rcases distSq_median_a_ab with ⟨hAB', hBC', hCA'⟩
  refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
  · calc distSq median_c_bc.A median_c_bc.B = 4/3 := hAB
      _ = distSq median_a_ab.C median_a_ab.A := by symm; exact hCA'
      _ = distSq median_a_ab.A median_a_ab.C := distSq_symm _ _
  · calc distSq median_c_bc.B median_c_bc.C = 1/3 := hBC
      _ = distSq median_a_ab.B median_a_ab.C := hBC'.symm
      _ = distSq median_a_ab.C median_a_ab.B := distSq_symm _ _
  · calc distSq median_c_bc.C median_c_bc.A = 1 := hCA
      _ = distSq median_a_ab.A median_a_ab.B := hAB'.symm
      _ = distSq median_a_ab.B median_a_ab.A := distSq_symm _ _

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

/- Barycentric ordering lemmas for interior points of each median triangle -/

lemma ordering_median_a_ab (p : ℝ × ℝ) (hp : point_in_interior p median_a_ab) : ba p > bb p ∧ bb p > bc p := by
  rcases hp with ⟨u, v, w, hu, hv, hw, hsum, hx, hy⟩
  have hx' : p.1 = v + w := by
    rw [hx]; unfold median_a_ab mid_AB centroid; simp
  have hy' : p.2 = w*(Real.sqrt 3 / 3) := by
    rw [hy]; unfold median_a_ab mid_AB centroid; simp
  dsimp [ba, bb, bc]
  rw [hx', hy']
  have h_ba_bb : (1 - (v + w)/2 - (w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) > ((v + w)/2 - (w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) := by
    have h_eq : (1 - (v + w)/2 - (w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) - ((v + w)/2 - (w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) = u := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  have h_bb_bc : ((v + w)/2 - (w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) > (w*(Real.sqrt 3/3))/Real.sqrt 3 := by
    have h_eq : ((v + w)/2 - (w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) - (w*(Real.sqrt 3/3))/Real.sqrt 3 = v/2 := by
      field_simp [h_sq3_ne]; ring
    nlinarith
  exact ⟨h_ba_bb, h_bb_bc⟩

lemma ordering_median_a_ca (p : ℝ × ℝ) (hp : point_in_interior p median_a_ca) : ba p > bc p ∧ bc p > bb p := by
  rcases hp with ⟨u, v, w, hu, hv, hw, hsum, hx, hy⟩
  have hx' : p.1 = v + w/2 := by
    rw [hx]; unfold median_a_ca centroid mid_CA; simp; ring
  have hy' : p.2 = v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2) := by
    rw [hy]; unfold median_a_ca centroid mid_CA; simp
  dsimp [ba, bb, bc]
  rw [hx', hy']
  have h_ba_bc : (1 - (v + w/2)/2 - (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) > 
    (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/Real.sqrt 3 := by
    have h_eq : (1 - (v + w/2)/2 - (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) - 
      (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/Real.sqrt 3 = u := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  have h_bc_bb : (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/Real.sqrt 3 > 
    ((v + w/2)/2 - (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) := by
    have h_eq : (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/Real.sqrt 3 - 
      ((v + w/2)/2 - (v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) = w/2 := by
      field_simp [h_sq3_ne]; ring
    nlinarith
  exact ⟨h_ba_bc, h_bc_bb⟩

lemma ordering_median_b_ab (p : ℝ × ℝ) (hp : point_in_interior p median_b_ab) : bb p > ba p ∧ ba p > bc p := by
  rcases hp with ⟨u, v, w, hu, hv, hw, hsum, hx, hy⟩
  have hx' : p.1 = 2*u + v + w := by
    rw [hx]; unfold median_b_ab centroid mid_AB; simp; ring
  have hy' : p.2 = v*(Real.sqrt 3/3) := by
    rw [hy]; unfold median_b_ab centroid mid_AB; simp
  dsimp [ba, bb, bc]
  rw [hx', hy']
  have h_bb_ba : ((2*u + v + w)/2 - (v*(Real.sqrt 3/3))/(2*Real.sqrt 3)) > 
    (1 - (2*u + v + w)/2 - (v*(Real.sqrt 3/3))/(2*Real.sqrt 3)) := by
    have h_eq : ((2*u + v + w)/2 - (v*(Real.sqrt 3/3))/(2*Real.sqrt 3)) - 
      (1 - (2*u + v + w)/2 - (v*(Real.sqrt 3/3))/(2*Real.sqrt 3)) = u := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  have h_ba_bc : (1 - (2*u + v + w)/2 - (v*(Real.sqrt 3/3))/(2*Real.sqrt 3)) > (v*(Real.sqrt 3/3))/Real.sqrt 3 := by
    have h_eq : (1 - (2*u + v + w)/2 - (v*(Real.sqrt 3/3))/(2*Real.sqrt 3)) - (v*(Real.sqrt 3/3))/Real.sqrt 3 = w/2 := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  exact ⟨h_bb_ba, h_ba_bc⟩

lemma ordering_median_b_bc (p : ℝ × ℝ) (hp : point_in_interior p median_b_bc) : bb p > bc p ∧ bc p > ba p := by
  rcases hp with ⟨u, v, w, hu, hv, hw, hsum, hx, hy⟩
  have hx' : p.1 = 2*u + 3*v/2 + w := by
    rw [hx]; unfold median_b_bc mid_BC centroid; simp; ring
  have hy' : p.2 = v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3) := by
    rw [hy]; unfold median_b_bc mid_BC centroid; simp
  dsimp [ba, bb, bc]
  rw [hx', hy']
  have h_bb_bc : ((2*u + 3*v/2 + w)/2 - (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) > 
    (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/Real.sqrt 3 := by
    have h_eq : ((2*u + 3*v/2 + w)/2 - (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) - 
      (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/Real.sqrt 3 = u := by
      field_simp [h_sq3_ne]; ring
    nlinarith
  have h_bc_ba : (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/Real.sqrt 3 > 
    (1 - (2*u + 3*v/2 + w)/2 - (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) := by
    have h_eq : (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/Real.sqrt 3 - 
      (1 - (2*u + 3*v/2 + w)/2 - (v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) = v/2 := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  exact ⟨h_bb_bc, h_bc_ba⟩

lemma ordering_median_c_bc (p : ℝ × ℝ) (hp : point_in_interior p median_c_bc) : bc p > bb p ∧ bb p > ba p := by
  rcases hp with ⟨u, v, w, hu, hv, hw, hsum, hx, hy⟩
  have hx' : p.1 = u + v + 3*w/2 := by
    rw [hx]; unfold median_c_bc centroid mid_BC; simp; ring
  have hy' : p.2 = u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2) := by
    rw [hy]; unfold median_c_bc centroid mid_BC; simp
  dsimp [ba, bb, bc]
  rw [hx', hy']
  have h_bc_bb : (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/Real.sqrt 3 > 
    ((u + v + 3*w/2)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) := by
    have h_eq : (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/Real.sqrt 3 - 
      ((u + v + 3*w/2)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) = u := by
      field_simp [h_sq3_ne]; ring
    nlinarith
  have h_bb_ba : ((u + v + 3*w/2)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) > 
    (1 - (u + v + 3*w/2)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) := by
    have h_eq : ((u + v + 3*w/2)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) - 
      (1 - (u + v + 3*w/2)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/3) + w*(Real.sqrt 3/2))/(2*Real.sqrt 3)) = w/2 := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  exact ⟨h_bc_bb, h_bb_ba⟩

lemma ordering_median_c_ca (p : ℝ × ℝ) (hp : point_in_interior p median_c_ca) : bc p > ba p ∧ ba p > bb p := by
  rcases hp with ⟨u, v, w, hu, hv, hw, hsum, hx, hy⟩
  have hx' : p.1 = u + v/2 + w := by
    rw [hx]; unfold median_c_ca mid_CA centroid; simp; ring
  have hy' : p.2 = u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3) := by
    rw [hy]; unfold median_c_ca mid_CA centroid; simp
  dsimp [ba, bb, bc]
  rw [hx', hy']
  have h_bc_ba : (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/Real.sqrt 3 > 
    (1 - (u + v/2 + w)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) := by
    have h_eq : (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/Real.sqrt 3 - 
      (1 - (u + v/2 + w)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) = u := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  have h_ba_bb : (1 - (u + v/2 + w)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) > 
    ((u + v/2 + w)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) := by
    have h_eq : (1 - (u + v/2 + w)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) - 
      ((u + v/2 + w)/2 - (u*Real.sqrt 3 + v*(Real.sqrt 3/2) + w*(Real.sqrt 3/3))/(2*Real.sqrt 3)) = v/2 := by
      field_simp [h_sq3_ne]; ring; nlinarith
    nlinarith
  exact ⟨h_bc_ba, h_ba_bb⟩

/- Main pairwise disjointness lemma: the 6 orderings are mutually exclusive -/

lemma median_pairwise_disjoint : PairwiseInteriorDisjoint median_triples := by
  intro t1 ht1 t2 ht2 hne
  intro h
  rcases h with ⟨p, hp1, hp2⟩
  have h_sig : ∀ t : Triangle, t ∈ median_triples → point_in_interior p t →
    (ba p > bb p ∧ bb p > bc p) ∨ (ba p > bc p ∧ bc p > bb p) ∨
    (bb p > ba p ∧ ba p > bc p) ∨ (bb p > bc p ∧ bc p > ba p) ∨
    (bc p > bb p ∧ bb p > ba p) ∨ (bc p > ba p ∧ ba p > bb p) := by
    intro t ht hpt
    unfold median_triples at ht
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with (rfl|rfl|rfl|rfl|rfl|rfl)
    · exact Or.inl (ordering_median_a_ab p hpt)
    · exact Or.inr (Or.inl (ordering_median_a_ca p hpt))
    · exact Or.inr (Or.inr (Or.inl (ordering_median_b_ab p hpt)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (ordering_median_b_bc p hpt))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ordering_median_c_bc p hpt)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ordering_median_c_ca p hpt)))))
  have h_sig1 := h_sig t1 ht1 hp1
  have h_sig2 := h_sig t2 ht2 hp2
  have : t1 = t2 := by
    unfold median_triples at ht1 ht2
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht1 ht2
    rcases ht1 with (rfl|rfl|rfl|rfl|rfl|rfl)
    · rcases ordering_median_a_ab p hp1 with ⟨h1, h2⟩
      rcases ht2 with (rfl|rfl|rfl|rfl|rfl|rfl)
      · rfl
      · rcases ordering_median_a_ca p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_ca p hp2 with ⟨h1', h2'⟩; nlinarith
    · rcases ordering_median_a_ca p hp1 with ⟨h1, h2⟩
      rcases ht2 with (rfl|rfl|rfl|rfl|rfl|rfl)
      · rcases ordering_median_a_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rfl
      · rcases ordering_median_b_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_ca p hp2 with ⟨h1', h2'⟩; nlinarith
    · rcases ordering_median_b_ab p hp1 with ⟨h1, h2⟩
      rcases ht2 with (rfl|rfl|rfl|rfl|rfl|rfl)
      · rcases ordering_median_a_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_a_ca p hp2 with ⟨h1', h2'⟩; nlinarith
      · rfl
      · rcases ordering_median_b_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_ca p hp2 with ⟨h1', h2'⟩; nlinarith
    · rcases ordering_median_b_bc p hp1 with ⟨h1, h2⟩
      rcases ht2 with (rfl|rfl|rfl|rfl|rfl|rfl)
      · rcases ordering_median_a_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_a_ca p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rfl
      · rcases ordering_median_c_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_ca p hp2 with ⟨h1', h2'⟩; nlinarith
    · rcases ordering_median_c_bc p hp1 with ⟨h1, h2⟩
      rcases ht2 with (rfl|rfl|rfl|rfl|rfl|rfl)
      · rcases ordering_median_a_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_a_ca p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rfl
      · rcases ordering_median_c_ca p hp2 with ⟨h1', h2'⟩; nlinarith
    · rcases ordering_median_c_ca p hp1 with ⟨h1, h2⟩
      rcases ht2 with (rfl|rfl|rfl|rfl|rfl|rfl)
      · rcases ordering_median_a_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_a_ca p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_ab p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_b_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rcases ordering_median_c_bc p hp2 with ⟨h1', h2'⟩; nlinarith
      · rfl
  exact hne this

/- subset_T: all vertices of each median triangle are in E -/

lemma centroid_mem_E : point_in_triangle centroid equilateral_side_two := by
  rw [mem_equilateral_iff]
  dsimp [centroid, ba, bb, bc]
  have h_sq3 : Real.sqrt 3 ≠ 0 := by positivity
  have h_ba : 1 - 1/2 - (Real.sqrt 3 / 3)/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bb : 1/2 - (Real.sqrt 3 / 3)/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bc : (Real.sqrt 3 / 3)/Real.sqrt 3 ≥ 0 := by
    field_simp [h_sq3]; norm_num
  exact ⟨h_ba, h_bb, h_bc⟩

lemma mid_AB_mem_E : point_in_triangle mid_AB equilateral_side_two := by
  rw [mem_equilateral_iff]
  dsimp [mid_AB, ba, bb, bc]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

lemma mid_BC_mem_E : point_in_triangle mid_BC equilateral_side_two := by
  rw [mem_equilateral_iff]
  dsimp [mid_BC, ba, bb, bc]
  have h_sq3 : Real.sqrt 3 ≠ 0 := by positivity
  have h_ba : 1 - (3/2)/2 - (Real.sqrt 3 / 2)/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bb : (3/2)/2 - (Real.sqrt 3 / 2)/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bc : (Real.sqrt 3 / 2)/Real.sqrt 3 ≥ 0 := by
    field_simp [h_sq3]; norm_num
  exact ⟨h_ba, h_bb, h_bc⟩

lemma mid_CA_mem_E : point_in_triangle mid_CA equilateral_side_two := by
  rw [mem_equilateral_iff]
  dsimp [mid_CA, ba, bb, bc]
  have h_sq3 : Real.sqrt 3 ≠ 0 := by positivity
  have h_ba : 1 - (1/2)/2 - (Real.sqrt 3 / 2)/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bb : (1/2)/2 - (Real.sqrt 3 / 2)/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bc : (Real.sqrt 3 / 2)/Real.sqrt 3 ≥ 0 := by
    field_simp [h_sq3]; norm_num
  exact ⟨h_ba, h_bb, h_bc⟩

lemma vertex_A_mem_E : point_in_triangle (0,0) equilateral_side_two := by
  rw [mem_equilateral_iff]
  dsimp [ba, bb, bc]; norm_num

lemma vertex_B_mem_E : point_in_triangle (2,0) equilateral_side_two := by
  rw [mem_equilateral_iff]
  dsimp [ba, bb, bc]; norm_num

lemma vertex_C_mem_E : point_in_triangle (1, Real.sqrt 3) equilateral_side_two := by
  rw [mem_equilateral_iff]
  dsimp [ba, bb, bc]
  have h_sq3 : Real.sqrt 3 ≠ 0 := by positivity
  have h_ba : 1 - 1/2 - Real.sqrt 3/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bb : 1/2 - Real.sqrt 3/(2*Real.sqrt 3) ≥ 0 := by
    field_simp [h_sq3]; norm_num
  have h_bc : Real.sqrt 3/Real.sqrt 3 ≥ 0 := by
    field_simp [h_sq3]; norm_num
  exact ⟨h_ba, h_bb, h_bc⟩

lemma median_a_ab_vertices_in_E : point_in_triangle median_a_ab.A equilateral_side_two ∧
  point_in_triangle median_a_ab.B equilateral_side_two ∧
  point_in_triangle median_a_ab.C equilateral_side_two := by
  unfold median_a_ab; simp; exact ⟨vertex_A_mem_E, mid_AB_mem_E, centroid_mem_E⟩

lemma median_a_ca_vertices_in_E : point_in_triangle median_a_ca.A equilateral_side_two ∧
  point_in_triangle median_a_ca.B equilateral_side_two ∧
  point_in_triangle median_a_ca.C equilateral_side_two := by
  unfold median_a_ca; simp; exact ⟨vertex_A_mem_E, centroid_mem_E, mid_CA_mem_E⟩

lemma median_b_ab_vertices_in_E : point_in_triangle median_b_ab.A equilateral_side_two ∧
  point_in_triangle median_b_ab.B equilateral_side_two ∧
  point_in_triangle median_b_ab.C equilateral_side_two := by
  unfold median_b_ab; simp; exact ⟨vertex_B_mem_E, centroid_mem_E, mid_AB_mem_E⟩

lemma median_b_bc_vertices_in_E : point_in_triangle median_b_bc.A equilateral_side_two ∧
  point_in_triangle median_b_bc.B equilateral_side_two ∧
  point_in_triangle median_b_bc.C equilateral_side_two := by
  unfold median_b_bc; simp; exact ⟨vertex_B_mem_E, mid_BC_mem_E, centroid_mem_E⟩

lemma median_c_bc_vertices_in_E : point_in_triangle median_c_bc.A equilateral_side_two ∧
  point_in_triangle median_c_bc.B equilateral_side_two ∧
  point_in_triangle median_c_bc.C equilateral_side_two := by
  unfold median_c_bc; simp; exact ⟨vertex_C_mem_E, centroid_mem_E, mid_BC_mem_E⟩

lemma median_c_ca_vertices_in_E : point_in_triangle median_c_ca.A equilateral_side_two ∧
  point_in_triangle median_c_ca.B equilateral_side_two ∧
  point_in_triangle median_c_ca.C equilateral_side_two := by
  unfold median_c_ca; simp; exact ⟨vertex_C_mem_E, mid_CA_mem_E, centroid_mem_E⟩

lemma median_subset_T (t : Triangle) (ht : t ∈ median_triples) : point_in_triangle t.A equilateral_side_two ∧
  point_in_triangle t.B equilateral_side_two ∧ point_in_triangle t.C equilateral_side_two := by
  unfold median_triples at ht
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with (rfl|rfl|rfl|rfl|rfl|rfl)
  · exact median_a_ab_vertices_in_E
  · exact median_a_ca_vertices_in_E
  · exact median_b_ab_vertices_in_E
  · exact median_b_bc_vertices_in_E
  · exact median_c_bc_vertices_in_E
  · exact median_c_ca_vertices_in_E

/- cover_T: E's three vertices appear among the median piece vertices -/

lemma E_A_in_biUnion : equilateral_side_two.A ∈ Finset.biUnion median_triples (λ t => {t.A, t.B, t.C}) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨median_a_ab, by unfold median_triples; simp, ?_⟩
  simp [equilateral_side_two, median_a_ab]

lemma E_B_in_biUnion : equilateral_side_two.B ∈ Finset.biUnion median_triples (λ t => {t.A, t.B, t.C}) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨median_b_ab, by unfold median_triples; simp, ?_⟩
  simp [equilateral_side_two, median_b_ab]

lemma E_C_in_biUnion : equilateral_side_two.C ∈ Finset.biUnion median_triples (λ t => {t.A, t.B, t.C}) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨median_c_bc, by unfold median_triples; simp, ?_⟩
  simp [equilateral_side_two, median_c_bc]

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
    subset_T := median_subset_T
    cover_T := ⟨E_A_in_biUnion, E_B_in_biUnion, E_C_in_biUnion⟩
    pairwise_disjoint := median_pairwise_disjoint
  }

lemma classification_forward (n : ℕ) (h : GeometricTriangleTilable n) :
  (∃ a b, a^2 + b^2 = n) ∨ (∃ a, 2*a^2 = n) ∨ (∃ a, 3*a^2 = n) ∨ (∃ a, 6*a^2 = n) ∨ (∃ a, a^2 = n) := by
  sorry

lemma not_geometric_tilable_7 : ¬ GeometricTriangleTilable 7 := by
  sorry

lemma not_geometric_tilable_11 : ¬ GeometricTriangleTilable 11 := by
  sorry

lemma conjectured_geometric_obstruction (p : ℕ) (hp : Nat.Prime p) (hp3 : p % 4 = 3) : ¬ GeometricTriangleTilable p := by
  sorry

-- EVOLVE-BLOCK-END

end Erdos634
