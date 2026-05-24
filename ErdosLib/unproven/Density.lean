import Mathlib

open Filter Finset Real Set
open scoped Topology

/-!
# Density Definitions

Natural (asymptotic) density and logarithmic density for subsets of ℕ.
-/

namespace ErdosLib

/-- Natural (asymptotic) density: limit of |A ∩ [0,n]| / n as n → ∞.
    If the limit exists, A is said to have density d. -/
noncomputable def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card : ℝ) / (n : ℝ)) atTop (𝓝 d)

/-- Upper natural density: limsup of |A ∩ [0,n]| / n. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  atTop.limsup (fun n : ℕ => ((Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card : ℝ) / (n : ℝ))

/-- Lower natural density: liminf of |A ∩ [0,n]| / n. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ => ((Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card : ℝ) / (n : ℝ))

/-- Logarithmic density: limit of (1 / log n) · Σ_{k ≤ n, k ∈ A} 1/k.
    Weaker than natural density: HasDensity A d → HasLogDensity A d. -/
noncomputable def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ =>
    ((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 d)

/-- Upper logarithmic density. -/
noncomputable def upperLogDensity (A : Set ℕ) : ℝ :=
  atTop.limsup (fun n : ℕ =>
    ((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ))

/-- Lower logarithmic density. -/
noncomputable def lowerLogDensity (A : Set ℕ) : ℝ :=
  atTop.liminf (fun n : ℕ =>
    ((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ))

lemma hasDensity_iff (A : Set ℕ) (d : ℝ) : HasDensity A d ↔
    ∀ ε > 0, ∀ᶠ n in atTop, |((Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card : ℝ) / (n : ℝ) - d| < ε := by
  rw [Metric.tendsto_nhds, HasDensity]
  simp

lemma hasLogDensity_iff (A : Set ℕ) (d : ℝ) : HasLogDensity A d ↔
    ∀ ε > 0, ∀ᶠ n in atTop,
      |((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ) - d| < ε := by
  rw [Metric.tendsto_nhds, HasLogDensity]
  simp

/-- Subset preserves upper densities. -/
lemma subset_upperDensity_le {A B : Set ℕ} (h : A ⊆ B) : upperDensity A ≤ upperDensity B := by
  refine limsup_le_limsup (Filter.eventually_of_forall (λ n => ?_)) Filter.atTop Filter.atTop
  have h_card : (Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card ≤
    (Finset.filter (λ k => k ∈ B) (Finset.range (n+1))).card :=
    Finset.card_le_card (Finset.filter_subset (λ k => k ∈ A) (Finset.range (n+1)))
  have hA : ((Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card : ℝ) / (n : ℝ) ≤
    ((Finset.filter (λ k => k ∈ B) (Finset.range (n+1))).card : ℝ) / (n : ℝ) := by
    refine (div_le_div_right (by exact_mod_cast Nat.zero_le _)).mpr ?_
    exact_mod_cast h_card
  exact hA

/-- Finite sets have density 0. -/
lemma finite_has_density_zero {S : Set ℕ} (hS : S.Finite) : HasDensity S 0 := by
  dsimp [HasDensity]
  have hS_bdd : ∃ M : ℕ, ∀ x ∈ S, x ≤ M := by
    by_cases h_empty : S = ∅
    · subst h_empty; exact ⟨0, λ x hx => False.elim hx⟩
    · have h_nonempty : (hS.toFinset).Nonempty := by
        rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨x, hx⟩
        exact ⟨x, hS.mem_toFinset.mpr hx⟩
      refine ⟨hS.toFinset.max' h_nonempty, λ x hx => ?_⟩
      have hx' : x ∈ hS.toFinset := hS.mem_toFinset.mpr hx
      exact Finset.le_max' hS.toFinset x hx'
  rcases hS_bdd with ⟨M, hM⟩
  have hcard_stable : ∀ n ≥ M, (Finset.filter (λ k => k ∈ S) (Finset.range (n+1))).card = (hS.toFinset).card := by
    intro n hn
    have h_eq : (Finset.filter (λ k => k ∈ S) (Finset.range (n+1))) = hS.toFinset := by
      ext x; constructor
      · intro hx; exact hS.mem_toFinset.mpr (by simpa [Finset.mem_filter] using hx)
      · intro hx
        have hx_S : x ∈ S := hS.mem_toFinset.mp hx
        have hx_le_n : x ≤ n := le_trans (hM x hx_S) hn
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hx_S⟩
    simp [h_eq]
  have h_nonneg : ∀ n : ℕ, 0 ≤ ((Finset.filter (λ k => k ∈ S) (Finset.range (n+1))).card : ℝ) / (n : ℝ) := by
    intro n; positivity
  have h_upper : ∀ n : ℕ, ((Finset.filter (λ k => k ∈ S) (Finset.range (n+1))).card : ℝ) / (n : ℝ) ≤
    ((hS.toFinset).card : ℝ) / (n : ℝ) := by
    intro n
    have h_card_le : (Finset.filter (λ k => k ∈ S) (Finset.range (n+1))).card ≤ (hS.toFinset).card := by
      by_cases hnM : n ≥ M
      · simp [hcard_stable n hnM]
      · refine Finset.card_le_card (λ x hx => hS.mem_toFinset.mpr ?_)
        simpa [Finset.mem_filter] using hx
    exact (div_le_div_right (by positivity)).mpr (mod_cast h_card_le)
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_c_div_n : Tendsto (fun (n : ℕ) => ((hS.toFinset).card : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (λ _ : ℕ => ((hS.toFinset).card : ℝ)) atTop _).mul
        (tendsto_inv_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_zero h_c_div_n h_nonneg h_upper

/-- Alternate formulation of log density using Finset.Icc 1 N instead of range (n+1). -/
noncomputable def S (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ k in Finset.filter (λ k => k ∈ A) (Finset.Icc 1 N), (k : ℝ)⁻¹

lemma S_equiv (A : Set ℕ) (d : ℝ) : HasLogDensity A d ↔
    Tendsto (fun N : ℕ => S A N / Real.log (N : ℝ)) atTop (𝓝 d) := by
  dsimp [HasLogDensity, S]
  constructor
  · intro h; simpa [Finset.Icc, Finset.range_succ] using h
  · intro h; simpa [Finset.Icc, Finset.range_succ] using h

/-- Inequality: y/(1+y) ≤ log(1+y) for y > -1, y ≠ 0. -/
lemma log_one_add_x_ge_x_div_one_add_x {y : ℝ} (hy : y > -1) (hy0 : y ≠ 0) : y / (1 + y) ≤ Real.log (1 + y) := by
  have hx : 1 / (1 + y) > 0 := by
    refine div_pos (by norm_num) (sub_pos.mpr ?_)
    nlinarith
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div, Real.log_one, sub_eq_add_neg, add_comm, ← sub_eq_add_neg] at h
  have h' : 1 / (1 + y) - 1 = -(y / (1 + y)) := by
    field_simp [show (1 + y) ≠ 0 from by nlinarith]
    ring
  rw [h'] at h
  linarith

/-- Natural density implies logarithmic density (via Abel summation). -/
lemma nat_density_imp_log_density {A : Set ℕ} {d : ℝ} (h : HasDensity A d) : HasLogDensity A d := by
  -- Standard analytic number theory result:
  -- Let a(n) = |A ∩ [0,n]|. Then a(n)/n → d.
  -- By Abel summation: Σ_{k∈A, k≤N} 1/k = a(N)/(N+1) + Σ_{n=1}^{N} a(n)/(n(n+1))
  -- Since a(n) ≈ dn, the RHS → d·log N, so dividing by log N gives d.
  sorry

end ErdosLib
