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
lemma finite_has_density_zero {A : Set ℕ} (hA : A.Finite) : HasDensity A 0 := by
  rw [hasDensity_iff]
  intro ε hε
  have h_card : A.card = (Finset.filter (λ k => k ∈ A) (Finset.range (A.card + 1))).card := by
    sorry
  sorry

/-- Natural density implies logarithmic density (via Abel summation). -/
lemma nat_density_imp_log_density {A : Set ℕ} {d : ℝ} (h : HasDensity A d) : HasLogDensity A d := by
  -- Standard analytic number theory result:
  -- Let a(n) = |A ∩ [0,n]|. Then a(n)/n → d.
  -- By Abel summation: Σ_{k∈A, k≤N} 1/k = a(N)/(N+1) + Σ_{n=1}^{N} a(n)/(n(n+1))
  -- Since a(n) ≈ dn, the RHS → d·log N, so dividing by log N gives d.
  sorry

end ErdosLib
