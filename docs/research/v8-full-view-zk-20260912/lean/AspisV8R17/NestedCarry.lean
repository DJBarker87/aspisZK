import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-! A symbolic expansion of a nested carry/read recurrence.

This is a pure field identity.  It does not identify binary indices, Rust
field words, challenge sampling, or a complete protocol functional. -/
set_option autoImplicit false
open Finset
namespace AspisV8R17

variable {F : Type*} [Field F]

def nested (h : F) (r : Nat → F) (z : F) : Nat → F
  | 0 => z
  | k + 1 => h * (r 0 + nested h (fun t => r (t + 1)) z k)

lemma sum_range_shift (f : Nat → F) (k : Nat) :
    (∑ t ∈ range k, f (t + 1)) + f 0 = ∑ t ∈ range (k + 1), f t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, sum_range_succ]
      calc
        (∑ x ∈ range k, f (x + 1)) + f (k + 1) + f 0 =
            ((∑ x ∈ range k, f (x + 1)) + f 0) + f (k + 1) := by ring
        _ = (∑ x ∈ range (k + 1), f x) + f (k + 1) := by rw [ih]

theorem nested_eq_sum (h : F) (r : Nat → F) (z : F) (k : Nat) :
    nested h r z k = (∑ t ∈ range k, r t * h ^ (t + 1)) + z * h ^ k := by
  induction k generalizing r with
  | zero => simp [nested]
  | succ k ih =>
      simp only [nested]
      rw [ih (r := fun t => r (t + 1))]
      let f : Nat → F := fun t => r t * h ^ (t + 1)
      have hs := sum_range_shift f k
      simp only [f] at hs ⊢
      have hdist : h * (∑ t ∈ range k, r (t + 1) * h ^ (t + 1)) =
          ∑ t ∈ range k, r (t + 1) * h ^ (t + 2) := by
        have aux : ∀ n, h * (∑ t ∈ range n, r (t + 1) * h ^ (t + 1)) =
            ∑ t ∈ range n, r (t + 1) * h ^ (t + 2) := by
          intro n
          induction n with
          | zero => simp
          | succ n ih =>
              rw [sum_range_succ, sum_range_succ, mul_add, ih]
              simp only [pow_succ]
              ring
        exact aux k
      have hsum : (∑ t ∈ range k, r (t + 1) * h ^ (t + 2)) + r 0 * h =
          ∑ t ∈ range (k + 1), r t * h ^ (t + 1) := by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hs
      rw [sum_range_succ]
      calc
        h * (r 0 + ((∑ t ∈ range k, r (t + 1) * h ^ (t + 1)) + z * h ^ k)) =
            (∑ t ∈ range k, r (t + 1) * h ^ (t + 2)) + r 0 * h + z * h ^ (k + 1) := by
              rw [mul_add, mul_add, hdist]
              simp only [pow_succ]
              ring
        _ = (∑ t ∈ range k, r t * h ^ (t + 1)) + r k * h ^ (k + 1) + z * h ^ (k + 1) := by
              rw [hsum, sum_range_succ]

theorem nested_half_eq_sum (r : Nat → F) (z : F) (k : Nat) :
    nested (1 / 2 : F) r z k =
      (∑ t ∈ range k, r t * (1 / 2 : F) ^ (t + 1)) + z * (1 / 2 : F) ^ k :=
  nested_eq_sum (1 / 2 : F) r z k

#print axioms nested_eq_sum
#print axioms nested_half_eq_sum
end AspisV8R17
