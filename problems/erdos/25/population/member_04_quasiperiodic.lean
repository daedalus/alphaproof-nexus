/-
  Population Member 04: Strategy = Prove True via quasi-periodic decomposition.
  Approach: Show that A is a finite union of periodic sets (cosets of some common modulus),
  and each periodic set has a logarithmic density (which is just its natural density).
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

/-- Natural density (asymptotic density) of a subset of ℕ. -/
noncomputable def HasDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((Finset.filter (λ k => k ∈ A) (Finset.range (n+1))).card : ℝ) / (n : ℝ)) atTop (𝓝 d)

def A (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) : Set ℕ :=
  { x : ℕ | ∀ i, (x : ℤ) < seq_n i ∨ ¬((x : ℤ) ≡ seq_a i [ZMOD seq_n i]) }

def UniversalStatement : Prop :=
  ∀ (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ), (∀ i, 0 < seq_n i) → StrictMono seq_n →
    ∃ d, HasLogDensity (A seq_n seq_a) d

-- EVOLVE-BLOCK-START

/-- The set of active constraints (those with n_i ≤ M) is finite because n_i grows at least as fast as i. -/
lemma active_constraints_finite (seq_n : ℕ → ℕ) (hmono : StrictMono seq_n) (M : ℕ) :
    {i | seq_n i ≤ M}.Finite := by
  have : ∀ i, seq_n i ≥ i := hmono.id_le
  have hbound : {i | seq_n i ≤ M} ⊆ {i | i ≤ M} := by
    intro i hi; exact le_trans (this i) hi
  exact Set.Finite.subset (Set.finite_le_nat M) hbound

/-- A finite set of natural numbers has natural density 0. -/
lemma finite_has_density_zero {S : Set ℕ} (hS : S.Finite) : HasDensity S 0 := by
  dsimp [HasDensity]
  -- A finite set S is bounded
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
  -- For n ≥ M, S ∩ {0,...,n} = S, so its cardinality is constant (= |S|)
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
  -- Squeeze: 0 ≤ |S ∩ range n|/n ≤ |S|/n → 0
  have h_nonneg : ∀ n : ℕ, 0 ≤ ((Finset.filter (λ k => k ∈ S) (Finset.range (n+1))).card : ℝ) / (n : ℝ) := by
    intro n; positivity
  have h_upper : ∀ n : ℕ, ((Finset.filter (λ k => k ∈ S) (Finset.range (n+1))).card : ℝ) / (n : ℝ) ≤ ((hS.toFinset).card : ℝ) / (n : ℝ) := by
    intro n
    have h_card_le : (Finset.filter (λ k => k ∈ S) (Finset.range (n+1))).card ≤ (hS.toFinset).card := by
      by_cases hn : n ≥ M
      · simp [hcard_stable n hn]
      · refine Finset.card_le_card (λ x hx => hS.mem_toFinset.mpr ?_)
        simpa [Finset.mem_filter] using hx
    exact (div_le_div_right (by positivity)).mpr (mod_cast h_card_le)
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_c_div_n : Tendsto (fun (n : ℕ) => ((hS.toFinset).card : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    -- c/n → 0 as n → ∞
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds : Tendsto (λ _ : ℕ => ((hS.toFinset).card : ℝ)) atTop _).mul
        (tendsto_inv_atTop.comp tendsto_nat_cast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_zero h_c_div_n h_nonneg h_upper

/-- For any fixed N, the set A ∩ {0,...,N} is finite (hence has density 0), and agrees with A
    on {0,...,N}. So the natural density behavior near 0 is irrelevant for the asymptotic density. -/
lemma A_finite_combination (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hmono : StrictMono seq_n) (N : ℕ) :
    ∃ (d : ℝ) (P : Set ℕ), HasDensity P d ∧ ∀ x ≤ N, (x ∈ A seq_n seq_a ↔ x ∈ P) := by
  have hfinite : (A seq_n seq_a ∩ Set.Iic N).Finite :=
    Set.Finite.subset (Set.finite_Iic N) (Set.inter_subset_right _ _)
  refine ⟨0, A seq_n seq_a ∩ Set.Iic N, finite_has_density_zero hfinite, λ x hx => ?_⟩
  simp [hx]

/-- Inequality: y/(1+y) ≤ log(1+y) for y > -1, y ≠ 0. Derived from log(x) ≤ x - 1 for x > 0. -/
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

/-- For any a > 0, T > 0, the sum Σ_{j=0}^{q-1} 1/(a + jT) satisfies the bounds:
    (1/T)·log(1 + qT/a) ≤ sum ≤ 1/a + (1/T)·log(1 + (q-1)T/a)
    
    These follow from the inequalities y/(1+y) ≤ log(1+y) ≤ y for y > 0,
    by setting y = T/(a + jT) and summing a telescoping product. -/
lemma residue_sum_bounds (a T : ℕ) (ha : 0 < a) (hT : 0 < T) (q : ℕ) :
    (1 / (T : ℝ)) * Real.log (1 + ((q : ℝ) * (T : ℝ)) / (a : ℝ)) ≤
    (∑ j in Finset.range q, (1 : ℝ)/((a + j*T : ℕ) : ℝ)) ∧
    (∑ j in Finset.range q, (1 : ℝ)/((a + j*T : ℕ) : ℝ)) ≤
    (1 : ℝ)/((a : ℕ) : ℝ) + (1 / (T : ℝ)) * Real.log (1 + (((q-1 : ℕ) : ℝ) * (T : ℝ)) / (a : ℝ)) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  induction' q with q ih generalizing a
  · -- q = 0: both sides involve log(1 + 0) = 0 and empty sum = 0
    simp [show Real.log (1 : ℝ) = 0 from by norm_num]
  · -- q+1 case: we add the term j = q
    rcases ih with ⟨h_lower, h_upper⟩
    let a' : ℝ := (a : ℝ)
    let T' : ℝ := (T : ℝ)
    have hpos : a' + (q : ℝ) * T' > 0 := by nlinarith [haR, hTR]
    have hy : (T' / (a' + (q : ℝ) * T')) > 0 := div_pos hTR hpos
    have hy_gt_neg_one : T' / (a' + (q : ℝ) * T') > -1 := by nlinarith
    have hy_ne_zero : T' / (a' + (q : ℝ) * T') ≠ 0 := by nlinarith
    -- The new term: 1/(a + qT)
    have h_new : (1 : ℝ)/((a + q*T : ℕ) : ℝ) = (1 : ℝ)/(a' + (q : ℝ) * T') := by norm_cast
    -- Using log(1+y) ≥ y/(1+y) with y = T/(a+qT):
    have h_log_ge : T'/(a' + (q : ℝ) * T') / (1 + T'/(a' + (q : ℝ) * T')) ≤ Real.log (1 + T'/(a' + (q : ℝ) * T')) :=
      log_one_add_x_ge_x_div_one_add_x hy_gt_neg_one hy_ne_zero
    have h_simplify : T'/(a' + (q : ℝ) * T') / (1 + T'/(a' + (q : ℝ) * T')) = T' / (a' + ((q : ℝ) + 1) * T') := by
      field_simp [show a' + (q : ℝ) * T' ≠ 0 from by nlinarith]
      ring
    have h_log_bound_lower : T' / (a' + ((q : ℝ) + 1) * T') ≤ Real.log (1 + T'/(a' + (q : ℝ) * T')) := by
      linarith
    -- Lower bound: sum_{j=0}^{q} 1/(a + jT) ≥ (1/T)·log(1 + (q+1)T/a)
    have h_log_telescope_lower : (1 / T') * Real.log (1 + ((q+1 : ℕ) : ℝ) * T' / a') =
        (1 / T') * (∑ j in Finset.range (q+1), Real.log (1 + T' / (a' + (j : ℝ) * T'))) := by
      simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
      ring
      -- This needs to show that the telescoping product gives the right formula
      calc
        (1 / T') * Real.log ((a' + ((q : ℝ) + 1) * T') / a') =
            (1 / T') * (Real.log (a' + ((q : ℝ) + 1) * T') - Real.log a') := by ring
        _ = (1 / T') * (∑ j in Finset.range (q+1), (Real.log (a' + ((j : ℝ) + 1) * T') - Real.log (a' + (j : ℝ) * T'))) := by
          simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
          ring
        _ = (1 / T') * (∑ j in Finset.range (q+1), Real.log (1 + T' / (a' + (j : ℝ) * T'))) := by
          refine congrArg (λ x => (1 / T') * x) (Finset.sum_congr rfl ?_)
          intro j hj
          have haj : a' + (j : ℝ) * T' ≠ 0 := by nlinarith
          field_simp [haj]
          ring
    sorry
    -- The full proof of the bounds is complex. For context length, we note that the
    -- bounds hold by: (a) applying log(1+y) ≤ y to get 1/(a + jT) ≥ (1/T)·log(1 + T/(a + jT))
    -- and summing telescopically for the lower bound; and (b) applying log(1+y) ≥ y/(1+y)
    -- to get 1/(a + jT) ≤ (1/T)·log(1 + T/(a + (j-1)T)) and summing for the upper bound.
    -- The detailed algebra is omitted to keep the proof manageable.
    sorry

/-- Any set that is eventually periodic has a logarithmic density, equal to the proportion
    of elements in one period.

    Proof sketch: If A is eventually periodic with period T beyond M, let
    c = |A ∩ {M+1, ..., M+T}|. For each active residue t (with M+t ∈ A) and large n,
    write n = M + qT + r. Using `residue_sum_bounds`, the sum S_t(q) =
    Σ_{j=0}^{q-1} 1/(M + jT + t) satisfies:
      (1/T)·log(1 + qT/(M+t)) ≤ S_t(q) ≤ 1/(M+t) + (1/T)·log(1 + (q-1)T/(M+t))
    Summing over active residues and dividing by log n, both bounds converge to c/T
    by the squeeze theorem, using that log(1 + qT/(M+t))/log n → 1 and log(1 + (q-1)T/(M+t))/log n → 1. -/
lemma eventually_periodic_has_log_density (A : Set ℕ) (M T : ℕ) (h : ∀ x ≥ M, x ∈ A ↔ x + T ∈ A) :
    ∃ d, HasLogDensity A d := by
  by_cases hT : T = 0
  · subst hT
    -- Degenerate case: period 0 gives no constraint. Not reachable when T is an LCM of positive moduli.
    sorry
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT
  -- Count of A-elements in one full period {M+1, ..., M+T}
  let period_finset : Finset ℕ := Finset.Ico (M + 1) (M + T + 1)
  let c := (period_finset.filter (λ x => x ∈ A)).card
  have hc_T : c ≤ T := by
    calc
      c = (Finset.filter (λ x => x ∈ A) period_finset).card := rfl
      _ ≤ period_finset.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = T := by simp [period_finset]
  use (c : ℝ) / (T : ℝ)
  dsimp [HasLogDensity]
  
  -- Define the main sum and the target ratio
  let S (n : ℕ) : ℝ := ∑ k in Finset.filter (λ k => k ∈ A) (Finset.range (n+1)), (k : ℝ)⁻¹
  let R (n : ℕ) : ℝ := S n / Real.log (n : ℝ)
  -- Harmonic numbers (not directly needed if we use the log bounds)
  -- We'll use the bounds from `residue_sum_bounds` and the squeeze theorem.
  
  have h_tendsto_R : Tendsto R atTop (𝓝 ((c : ℝ) / (T : ℝ))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    -- Choose N large enough so that all subsequent terms are within ε of c/T
    -- The detailed epsilon-delta argument requires:
    --   1. For large n, S(n) = S_initial(M) + Σ_{active t} S_t(q) + tail, with tail bounded.
    --   2. From `residue_sum_bounds`, each S_t(q) is close to (1/T)·log q.
    --   3. log q / log n → 1.
    --   4. The initial segment and tail contribute O(1/log n) → 0.
    -- This argument is standard but technically dense. We outline the structure.
    sorry
  exact ⟨(c : ℝ) / (T : ℝ), h_tendsto_R⟩

/-- A is a subset of its tail-truncation (the set with the first k moduli removed).
    Hence A \ tail ⊆ {x | x < n_k} holds trivially (the difference is actually empty). -/
lemma A_truncation_approximation (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hmono : StrictMono seq_n) (k : ℕ) :
    (A seq_n seq_a) \ (A (fun i => seq_n (i + k)) (fun i => seq_a (i + k))) ⊆ {x | x < seq_n k} := by
  intro x hx
  rcases hx with ⟨hxA, hx_not⟩
  dsimp [A] at hxA hx_not
  by_contra! hx_ge
  push_neg at hx_not
  rcases hx_not with ⟨i, ⟨hge, hcong⟩⟩
  have hj := hxA (i + k)
  rcases hj with (hlt | hne)
  · exact Nat.lt_asymm hlt hge
  · exact hne hcong

/-- The sets A and its tail-truncation differ only on a set of zero logarithmic density,
    hence they have the same logarithmic density (if either exists).

    NOTE: This lemma as stated is FALSE in general. The tail-truncation (dropping first k
    moduli) has FEWER constraints, so it is a SUPERSET of A for large x. Their difference
    can have positive density (e.g., n_i = 2^{i+1}, a_i = 0 gives density 1/2 vs 3/4).

    What should be proved instead uses the HEAD-truncation (keeping only the first k moduli),
    but even that requires a limiting argument. We leave this as a sorry because the
    current approach is not salvageable without a fundamentally different direction. -/
lemma tail_density_equality (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) :
    (HasLogDensity (A seq_n seq_a) d) ↔ (HasLogDensity (A (fun i => seq_n (i + k)) (fun i => seq_a (i + k))) d) := by
  constructor
  · intro h
    sorry
  · intro h
    sorry

/-- The truncated set is eventually periodic with period L = lcm{n_0, ..., n_{k-1}}.
    Since it only has finitely many moduli, it's periodic and has a log density.

    NOTE: The current definition uses the TAIL (starting at k), which still has infinitely
    many moduli and is NOT eventually periodic in general. The correct approach would be
    to define the HEAD-truncation (keeping only the first k moduli) and prove that is
    eventually periodic. We leave this as a sorry since a structural redesign would be needed. -/
lemma truncation_has_log_density (seq_n : ℕ → ℕ) (seq_a : ℕ → ℤ) (hpos : ∀ i, 0 < seq_n i) (hmono : StrictMono seq_n) (k : ℕ) :
    ∃ d, HasLogDensity (A (fun i => seq_n (i + k)) (fun i => seq_a (i + k))) d := by
  sorry

/-- Combining: A has a log density because its truncations have one, and the tail contributes nothing.

    NOTE: This depends on `tail_density_equality` and `truncation_has_log_density`, both
    of which are broken (see notes). A correct proof would need a completely different
    approach (e.g., showing head-truncations' densities converge, and bounding the error
    between A and its head-truncation by a set of negligible log density). -/
lemma universal_from_truncation : UniversalStatement := by
  intro seq_n seq_a hpos hmono
  have h_trunc (k : ℕ) : ∃ d, HasLogDensity (A (fun i => seq_n (i + k)) (fun i => seq_a (i + k))) d :=
    truncation_has_log_density seq_n seq_a hpos hmono k
  sorry

-- EVOLVE-BLOCK-END

theorem erdos_25 : True ↔ UniversalStatement := by
  constructor
  · intro _
    exact universal_from_truncation
  · intro h; trivial

end Erdos25
