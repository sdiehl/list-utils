import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace List

variable {α : Type*}

/-! ## Negation -/

/-- Sum of negated elements equals negation of sum.

This is the `List` analogue of `Multiset.sum_map_neg`. -/
theorem sum_map_neg (l : List α) (f : α → ℚ) :
    (l.map (fun x => -f x)).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih, add_comm]

/-- Sum of negated elements equals negation of sum (general version). -/
theorem sum_map_neg' {M : Type*} [AddCommGroup M] (l : List α) (f : α → M) :
    (l.map (fun x => -f x)).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]; abel

/-! ## Subtraction -/

/-- Sum distributes over subtraction in the mapped function.

This is the `List` analogue of `Finset.sum_sub_distrib`. -/
theorem sum_map_sub (l : List α) (f g : α → ℚ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]; ring

/-- Sum distributes over subtraction (general version). -/
theorem sum_map_sub' {M : Type*} [AddCommGroup M] (l : List α) (f g : α → M) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]; abel

/-! ## Scalar Multiplication -/

/-- Scalar multiplication distributes into sum.

Uses Mathlib's `List.smul_sum` under the hood. -/
theorem sum_mul_left (l : List α) (c : ℚ) (f : α → ℚ) :
    c * (l.map f).sum = (l.map (fun x => c * f x)).sum := by
  rw [← smul_eq_mul, List.smul_sum, List.map_map]
  simp only [smul_eq_mul, Function.comp_def]

/-- Scalar multiplication distributes into sum (right multiplication). -/
theorem sum_mul_right (l : List α) (c : ℚ) (f : α → ℚ) :
    (l.map f).sum * c = (l.map (fun x => f x * c)).sum := by
  rw [mul_comm, sum_mul_left]
  congr 1
  ext x
  ring_nf

/-! ## Additional Utilities -/

/-- Sum of constant function. -/
theorem sum_map_const (l : List α) (c : ℚ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons h t ih => simp only [map_cons, sum_cons, length_cons, Nat.cast_add, Nat.cast_one, ih]; ring

/-- Sum is additive over list append. -/
theorem sum_map_append (l₁ l₂ : List α) (f : α → ℚ) :
    ((l₁ ++ l₂).map f).sum = (l₁.map f).sum + (l₂.map f).sum := by
  simp [List.map_append]

/-! ## Existence Lemmas -/

/-- If sum of mapped non-negative values is positive, some element maps to positive. -/
theorem exists_pos_of_sum_pos (l : List α) (f : α → ℚ)
    (hnonneg : ∀ x ∈ l, 0 ≤ f x) (hpos : 0 < (l.map f).sum) :
    ∃ x ∈ l, 0 < f x := by
  by_contra hall
  push_neg at hall
  have hzero : ∀ x ∈ l, f x = 0 := fun x hx => le_antisymm (hall x hx) (hnonneg x hx)
  have hsum_zero : (l.map f).sum = 0 := by
    have heq : l.map f = l.map (fun _ => (0 : ℚ)) := List.map_congr_left hzero
    rw [heq]
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_zero]
  linarith

/-- If sum of mapped non-positive values is negative, some element maps to negative. -/
theorem exists_neg_of_sum_neg (l : List α) (f : α → ℚ)
    (hnonpos : ∀ x ∈ l, f x ≤ 0) (hneg : (l.map f).sum < 0) :
    ∃ x ∈ l, f x < 0 := by
  by_contra hall
  push_neg at hall
  have hzero : ∀ x ∈ l, f x = 0 := fun x hx => le_antisymm (hnonpos x hx) (hall x hx)
  have hsum_zero : (l.map f).sum = 0 := by
    have heq : l.map f = l.map (fun _ => (0 : ℚ)) := List.map_congr_left hzero
    rw [heq]
    simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_zero]
  linarith

/-- If sum is nonzero and all elements have the same sign, some element is nonzero. -/
theorem exists_ne_zero_of_sum_ne_zero (l : List α) (f : α → ℚ)
    (hsamesign : (∀ x ∈ l, 0 ≤ f x) ∨ (∀ x ∈ l, f x ≤ 0))
    (hne : (l.map f).sum ≠ 0) :
    ∃ x ∈ l, f x ≠ 0 := by
  rcases hsamesign with hnonneg | hnonpos
  · have hpos : 0 < (l.map f).sum := by
      rcases lt_trichotomy 0 (l.map f).sum with h | h | h
      · exact h
      · exact absurd h.symm hne
      · have hle : (l.map f).sum ≤ 0 := le_of_lt h
        have hge : 0 ≤ (l.map f).sum := List.sum_nonneg (fun x hx => by
          rw [List.mem_map] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          exact hnonneg a ha)
        exact absurd (le_antisymm hle hge) hne
    obtain ⟨x, hx, hfx⟩ := exists_pos_of_sum_pos l f hnonneg hpos
    exact ⟨x, hx, ne_of_gt hfx⟩
  · -- For nonpositive case, use negation to reduce to nonneg case
    have hneg : (l.map f).sum < 0 := by
      by_contra hnneg
      push_neg at hnneg
      have hle : (l.map f).sum ≤ 0 := by
        have hneg_nonneg : 0 ≤ (l.map (fun x => -f x)).sum := List.sum_nonneg (fun x hx => by
          rw [List.mem_map] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          exact neg_nonneg.mpr (hnonpos a ha))
        have heq : (l.map (fun x => -f x)).sum = -(l.map f).sum := sum_map_neg l f
        rw [heq] at hneg_nonneg
        linarith
      exact hne (le_antisymm hle hnneg)
    obtain ⟨x, hx, hfx⟩ := exists_neg_of_sum_neg l f hnonpos hneg
    exact ⟨x, hx, ne_of_lt hfx⟩

end List
