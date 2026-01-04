import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# List Utilities

Additional lemmas for `List` operations that complement Mathlib.

These lemmas fill gaps in Mathlib's List module - specifically around
sum operations with negation and subtraction that exist for `Multiset`
and `Finset` but not for `List`.

## Main Results

* `List.sum_map_neg` - Sum of negated elements equals negation of sum
* `List.sum_map_sub` - Sum distributes over subtraction in mapped function
* `List.sum_mul_left` - Scalar multiplication distributes into sum

## Usage

```lean
import ListUtils

example (l : List Nat) (f : Nat → ℚ) :
    (l.map (fun x => -f x)).sum = -(l.map f).sum :=
  List.sum_map_neg l f
```
-/

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
  ring

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

end List
