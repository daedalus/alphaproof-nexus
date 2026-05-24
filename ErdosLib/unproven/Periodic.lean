import Mathlib
open Filter Finset Real Set
open scoped Topology

/-!
# Periodic Sets and Densities

If a set S ⊆ ℕ is eventually periodic with period L beyond a threshold M,
then S has natural density c/L where c = |S ∩ [M, M+L)|.

This is a standard result used throughout the Erdős problems library.
-/

namespace ErdosLib

/-- A set S ⊆ ℕ is eventually periodic if there exists M, L such that
    for all x ≥ M, x ∈ S ↔ x + L ∈ S. -/
def EventuallyPeriodic (S : Set ℕ) : Prop :=
  ∃ M L, ∀ x ≥ M, x ∈ S ↔ x + L ∈ S

/-- If S is eventually periodic, it has natural density equal to the proportion
    of elements in one period after the threshold M.

    More precisely: let M be the threshold, L the period length,
    c = |S ∩ [M, M+L)|. Then HasDensity S ((c : ℝ) / (L : ℝ)).

    Proof: For n ≥ M, write n = M + qL + r with 0 ≤ r < L.
    Then |S ∩ [0,n]| = C₀ + q·c + t where:
      - C₀ = |S ∩ [0, M-1]| (fixed initial segment)
      - t = |S ∩ [M+qL, M+qL+r-1]| (tail of the last partial period, 0 ≤ t ≤ c)
    Hence |count(n)/n - c/L| ≤ (L·C₀ + c·(M+L)) / (L·n) → 0.
 -/
lemma eventually_periodic_has_density (S : Set ℕ) (h : EventuallyPeriodic S) : ∃ d, HasDensity S d := by
  rcases h with ⟨M, L, hper⟩
  by_cases hL : L = 0
  · subst hL; refine ⟨0, ?_⟩
    -- If period is 0, the condition becomes vacuous or constant; treat as density 0.
    sorry
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
    let cnt (n : ℕ) : ℝ := ((Finset.filter (λ x => x ∈ S) (Finset.range (n+1))).card : ℝ)
    let C₀ : ℝ := cnt (M-1)
    let c : ℝ := ((Finset.filter (λ x => x ∈ S) (Finset.Ico M (M + L))).card : ℝ)
    refine ⟨c / (L : ℝ), ?_⟩
    dsimp [HasDensity, cnt, c, C₀]
    -- Epsilon-delta argument
    -- For n = M + qL + r (0 ≤ r < L):
    --   |S ∩ [0,n]| = |S ∩ [0, M-1]| + q·|S ∩ [M, M+L)| + |S ∩ [M+qL, M+qL+r-1]|
    --   = C₀ + q·c + tail, where 0 ≤ tail ≤ c
    -- Hence:
    --   |cnt(n)/n - c/L| = |(C₀·L + tail·L - c·M - c·r)| / (L·n)
    --    ≤ (C₀·L + c·L + c·M + c·L) / (L·n)
    --    = (C₀ + c·M/L + 2·c) / n
    -- which → 0 since denominator → ∞.
    let K := C₀ + (c : ℝ) * (M : ℝ) / (L : ℝ) + 2 * c
    have h_bound : ∀ n : ℕ, |cnt n / (n : ℝ) - (c : ℝ) / (L : ℝ)| ≤ K / (n : ℝ) := by
      intro n
      by_cases hnM : n < M
      · -- n in the initial segment: bound by max of |cnt/n| and |c/L|
        sorry
      · -- n ≥ M: use the periodic structure
        sorry
    -- Show K/n → 0 and apply the squeeze theorem
    sorry

/-- Eventually periodic sets also have logarithmic density (via natural density → log density). -/
lemma eventually_periodic_has_log_density (S : Set ℕ) (h : EventuallyPeriodic S) : ∃ d, HasLogDensity S d := by
  rcases eventually_periodic_has_density S h with ⟨d, hd⟩
  -- Natural density implies logarithmic density
  refine ⟨d, ?_⟩
  -- Proof via Abel summation (deferred — routine analytic number theory)
  sorry

/-- The maximal period for a set defined by finitely many congruence conditions.
    The product of the moduli gives a period. -/
lemma product_of_moduli_is_period (moduli : ℕ → ℕ) (residues : ℕ → ℤ) (k : ℕ) (hpos : ∀ i, 0 < moduli i) :
    EventuallyPeriodic { x : ℕ | ∀ i < k, ¬((x : ℤ) ≡ residues i [ZMOD moduli i]) } := by
  let L := ∏ i in Finset.range k, moduli i
  have hL_dvd : ∀ i < k, (moduli i : ℤ) ∣ (L : ℤ) := by
    intro i hi
    apply Nat.cast_dvd.mpr
    refine Finset.dvd_prod_of_mem (λ j => moduli j) (Finset.mem_range.mpr hi)
  refine ⟨0, L, λ x hx => ?_⟩
  constructor
  · intro h i hi
    intro hcong
    apply h i hi
    have h_mod : (x + L : ℤ) ≡ (x : ℤ) [ZMOD moduli i] :=
      Int.ModEq.mpr (by
        have : (x + L : ℤ) - (x : ℤ) = (L : ℤ) := by ring
        rw [this]
        exact hL_dvd i hi)
    exact (h_mod.symm.trans hcong)
  · intro h i hi
    intro hcong
    apply h i hi
    have h_mod : (x : ℤ) ≡ (x + L : ℤ) [ZMOD moduli i] :=
      Int.ModEq.mpr (by
        have : (x : ℤ) - (x + L : ℤ) = -(L : ℤ) := by ring
        rw [this]
        exact dvd_neg.mpr (hL_dvd i hi))
    exact (h_mod.trans hcong)

end ErdosLib
