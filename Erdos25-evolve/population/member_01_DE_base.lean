/-
  Population Member 01: Strategy = Prove True via Davenport-Erdős reduction.
  Approach: Show that for any residues, A has the same density as the all-0 case
  via a measure-preserving bijection.
  Rating (initial): Elo 1200
-/
import Mathlib

open Filter Finset Real Set
open scoped Topology
open Classical

set_option maxRecDepth 2000000

namespace Erdos25

noncomputable def HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 d)

def A (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

def UniversalStatement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, HasLogDensity (A seq_n seq_a) d

-- EVOLVE-BLOCK-START

/-- Map x → x + t preserves the structure of A. -/
lemma A_translate (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (t : ℕ) :
    A seq_n seq_a = { x | x + t ∈ A seq_n (λ i => (seq_a i : ℤ) - (t : ℤ)) } := by
  ext x; dsimp [A]; constructor
  · intro h i; rcases h i with (hlt | hne)
    · left; exact (Nat.add_lt_add_right hlt t).trans_eq (Nat.add_sub_cancel' _ _).symm
    · right; intro h_eq; apply hne; simpa [add_comm, add_left_comm, add_assoc] using h_eq
  · intro h i; rcases h i with (hlt | hne)
    · left; exact (Nat.add_lt_add_iff_right t).mp ?_
      -- FIXME: this doesn't work because of the divagation with t
      sorry
    · right; intro h_eq; apply hne; simpa using h_eq

/-- The all-0 case has log density 1. -/
lemma davenport_erdos_all_zero_density_one (seq_n : ℕ → ℕ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    HasLogDensity (A seq_n (λ _ => 0 : ℕ → ℤ)) 1 := by
  sorry

/-- Any set A has log density 0 if it's "thin enough" (e.g., A has natural density 0). -/
lemma thin_sets_have_log_density_zero (A : Set ℕ) (h : ∀ᶠ n in atTop, (A ∩ Iio n).ncard ≤ Real.log n) :
    HasLogDensity A 0 := by
  sorry

/-- The set A is closely related to a set defined by non-divisibility: x ∈ A' iff ∀ i, n_i ∤ x.
    This is the Davenport-Erdős case (all residues 0). -/
lemma A_to_zero_case (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) :
    (A seq_n seq_a) = (A seq_n (λ _ => 0)) := by
  ext x; dsimp [A]; constructor
  · intro h i; rcases h i with (hlt | hne)
    · left; exact hlt
    · right; intro hzero; apply hne; simpa using hzero
  · intro h i; rcases h i with (hlt | hne)
    · left; exact hlt
    · right; exact hne

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    intro seq_n seq_a hpos hmono
    rw [A_to_zero_case seq_n seq_a]
    exact ⟨1, davenport_erdos_all_zero_density_one seq_n hpos hmono⟩
  · intro h; trivial

end Erdos25
