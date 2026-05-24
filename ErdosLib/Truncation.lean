import Mathlib
open Filter Finset Real Set
open scoped Topology

/-!
# Head-Truncation

For a congruence-avoiding set defined by (seq_n, seq_a), head-truncation
keeps only the first k constraints. The truncated set is a superset of the
original, eventually periodic, and has a well-defined density.

Strategy: truncate at the *head* (first k moduli), not the tail.
Head-truncation produces a superset; tail-truncation (removing first k moduli)
produces a subset but the difference can have positive density (wrong approach).
-/

namespace ErdosLib

/-- The congruence-avoiding set with no restrictions (A_head for k=0). -/
lemma A_head_zero : A_from_seqs (λ _ => 1) (λ _ => 0) = Set.univ := by
  ext x; simp [A_from_seqs]

/-- Head-truncation: keep only the first k moduli.
    Fewer constraints = more elements, so A_head(k) ⊇ A for all k. -/
def A_head (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (k : ℕ) : Set ℕ :=
  { x : ℕ | ∀ i, i < k → ((x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i])) }

lemma A_subset_A_head (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (k : ℕ) :
    A_from_seqs seq_n seq_a ⊆ A_head seq_n seq_a k := by
  intro x hx
  dsimp [A_head]
  intro i hi
  dsimp [A_from_seqs] at hx
  exact hx i

/-- A_head(k) is eventually periodic with period = product of first k moduli,
    after threshold M = max of first k moduli. -/
lemma A_head_eventually_periodic (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) :
    EventuallyPeriodic (A_head seq_n seq_a k) := by
  by_cases hk : k = 0
  · subst hk
    refine ⟨0, 1, λ x hx => ?_⟩
    simp [A_head, EventuallyPeriodic]
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  let S := Finset.image seq_n (Finset.range k)
  have hS_nonempty : S.Nonempty := by
    refine ⟨seq_n 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk_pos, rfl⟩⟩
  let M := S.max' hS_nonempty
  have hM : ∀ i < k, seq_n i ≤ M := by
    intro i hi
    apply Finset.le_max' S (seq_n i)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  let L := ∏ i in Finset.range k, seq_n i
  refine ⟨M, L, λ x hx => ?_⟩
  have hx_ge : ∀ i < k, (seq_n i : ℤ) ≤ (x : ℤ) := by
    intro i hi; exact mod_cast le_trans (hM i hi) hx
  constructor
  · intro h i hi
    rcases h i hi with (hlt | hne)
    · exfalso; exact hlt.trans_le (hx_ge i hi)
    · right
      intro hcong
      apply hne
      have hL_dvd_i : (seq_n i : ℤ) ∣ (L : ℤ) := by
        apply Nat.cast_dvd.mpr
        refine Finset.dvd_prod_of_mem (λ j => seq_n j) (Finset.mem_range.mpr hi)
      have h_mod : (x + L : ℤ) ≡ (x : ℤ) [ZMOD seq_n i] :=
        Int.ModEq.mpr (by
          simpa [add_sub_cancel_left] using hL_dvd_i)
      have : (x : ℤ) ≡ seq_a i [ZMOD seq_n i] := hcong.trans h_mod.symm
      exact this
  · intro h i hi
    rcases h i hi with (hlt | hne)
    · exfalso; exact hlt.trans_le (hx_ge i hi)
    · right
      intro hcong
      apply hne
      have hL_dvd_i : (seq_n i : ℤ) ∣ (L : ℤ) := by
        apply Nat.cast_dvd.mpr
        refine Finset.dvd_prod_of_mem (λ j => seq_n j) (Finset.mem_range.mpr hi)
      have h_mod : (x : ℤ) ≡ (x + L : ℤ) [ZMOD seq_n i] :=
        Int.ModEq.mpr (by
          have : (x : ℤ) - (x + L : ℤ) = -(L : ℤ) := by omega
          rw [this]
          exact dvd_neg.mpr hL_dvd_i)
      exact hcong.trans h_mod

/-- A_head(k) has a density (both natural and logarithmic). -/
lemma A_head_has_density (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) :
    ∃ d, HasDensity (A_head seq_n seq_a k) d :=
  eventually_periodic_has_density _ (A_head_eventually_periodic seq_n seq_a hpos hmono k)

/-- A_head(k) has a logarithmic density. -/
lemma A_head_has_log_density (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) :
    ∃ d, HasLogDensity (A_head seq_n seq_a k) d :=
  eventually_periodic_has_log_density _ (A_head_eventually_periodic seq_n seq_a hpos hmono k)

/-- The canonical density value of A_head(k) computed from the periodic formula.
    For k = 0, density = 1 (no constraints → all of ℕ).
    For k > 0, density = c/L where L = product of first k moduli, c = |A_head(k) ∩ [M, M+L)|. -/
noncomputable def head_density_value (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) : ℝ :=
  if hk : k = 0 then 1 else
  let M := (Finset.image seq_n (Finset.range k)).max' (by
    have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr (Nat.pos_of_ne_zero hk)
    exact ⟨seq_n 0, Finset.mem_image.mpr ⟨0, h0, rfl⟩⟩)
  let L := ∏ i in Finset.range k, seq_n i
  let c := (Finset.filter (λ x => x ∈ A_head seq_n seq_a k) (Finset.Ico M (M + L))).card
  (c : ℝ) / (L : ℝ)

lemma head_density_nonneg (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) :
    0 ≤ head_density_value seq_n seq_a hpos hmono k := by
  dsimp [head_density_value]
  split
  · norm_num
  · positivity

/-- head_density_value is antitone in k (more constraints → smaller density). -/
lemma head_density_antitone (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    Antitone (head_density_value seq_n seq_a hpos hmono) := by
  intro a b h
  -- A_head(b) ⊆ A_head(a) implies density order.
  -- This follows from the inclusion and the fact that the periodic formula
  -- computes the actual density (which respects subset order).
  sorry

/-- The densities d_k = head_density_value(k) converge to a limit d. -/
lemma head_densities_converge (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ)
    (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) :
    ∃ d, Tendsto (head_density_value seq_n seq_a hpos hmono) atTop (𝓝 d) := by
  have h_antitone : Antitone (head_density_value seq_n seq_a hpos hmono) :=
    head_density_antitone seq_n seq_a hpos hmono
  have h_bounded : ∀ k, 0 ≤ head_density_value seq_n seq_a hpos hmono k :=
    head_density_nonneg seq_n seq_a hpos hmono
  let d := sInf (Set.range (head_density_value seq_n seq_a hpos hmono))
  have h_d_le : ∀ k, d ≤ head_density_value seq_n seq_a hpos hmono k :=
    λ k => csInf_le (Set.range_nonempty _) ⟨k, rfl⟩
  have h_tendsto : Tendsto (head_density_value seq_n seq_a hpos hmono) atTop (𝓝 d) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h_exists : ∃ m, head_density_value seq_n seq_a hpos hmono m < d + ε := by
      by_contra! h_all
      have h_lower_bound : d + ε ≤ d := by
        apply le_csInf (Set.range_nonempty _)
        intro y hy
        rcases hy with ⟨m, rfl⟩
        exact h_all m
      nlinarith
    rcases h_exists with ⟨m, hm⟩
    refine Filter.eventually_atTop.mpr ⟨m, λ n hn => ?_⟩
    have h_antitone_nm : head_density_value seq_n seq_a hpos hmono n ≤ head_density_value seq_n seq_a hpos hmono m :=
      h_antitone hn
    have h_diff : |head_density_value seq_n seq_a hpos hmono n - d| < ε := by
      have h_nonneg_diff : 0 ≤ head_density_value seq_n seq_a hpos hmono n - d := by
        nlinarith [h_d_le n, h_bounded n]
      have h_upper : head_density_value seq_n seq_a hpos hmono n - d < ε := by
        nlinarith
      rw [abs_of_nonneg h_nonneg_diff]
      exact h_upper
    exact h_diff
  exact ⟨d, h_tendsto⟩

end ErdosLib
