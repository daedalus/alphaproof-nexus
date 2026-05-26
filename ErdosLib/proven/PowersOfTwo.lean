import Mathlib

open Finset

namespace ErdosLib

/-- The predicate that n is a power of two (including 1 = 2^0). -/
def is_power_of_two (n : ℕ) : Prop := ∃ e : ℕ, n = 2^e

/-- The set of all powers of two. -/
def powers_of_two_set : Set ℕ := { n | is_power_of_two n }

lemma is_power_of_two_iff (n : ℕ) : is_power_of_two n ↔ n ∈ powers_of_two_set := by
  rfl

lemma one_is_power_of_two : is_power_of_two 1 := ⟨0, by norm_num⟩

lemma two_is_power_of_two : is_power_of_two 2 := ⟨1, by norm_num⟩

lemma zero_not_power_of_two : ¬ is_power_of_two 0 := by
  rintro ⟨e, h⟩
  have : 2^e ≥ 1 := Nat.one_le_two_pow (n := e)
  omega

lemma pow_two_factor (e : ℕ) (he : e ≥ 1) : 2^e = 2 * (2^(e-1)) := by
  calc
    2^e = 2^((e-1)+1) := by rw [Nat.sub_add_cancel he]
    _ = 2^(e-1) * 2 := by rw [Nat.pow_succ]
    _ = 2 * 2^(e-1) := mul_comm _ _

/-- If n is even and n = 2^e, then e ≥ 1. -/
lemma even_power_of_two_implies_ge_one (n e : ℕ) (hn_even : 2 ∣ n) (h_eq : n = 2^e) : e ≥ 1 := by
  by_contra! h
  have : e = 0 := by omega
  subst this
  simp at h_eq
  subst h_eq
  have : ¬ 2 ∣ (1 : ℕ) := by norm_num
  exact this hn_even

/-- The minimal exponent for powers of two: 2^e ≥ 1 for all e. -/
lemma pow_two_pos (e : ℕ) : 1 ≤ 2^e :=
  Nat.one_le_two_pow (n := e)

/-- Powers of two grow with exponent. -/
lemma pow_two_strictMono : StrictMono (λ (e : ℕ) => 2^e) :=
  λ a b h => Nat.pow_lt_pow_right (by norm_num : 1 < 2) h

end ErdosLib
