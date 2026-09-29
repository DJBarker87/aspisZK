import Mathlib.Tactic

/-! Arithmetic leaves for source-derived endpoint fibres. The source table
enumeration is checked in Rust; this file does not claim Rust extraction. -/
set_option autoImplicit false
namespace AspisV8R19.SelectorGather
def p : Nat := 2147483647
def canonicalSum (xs : List Nat) : Nat :=
  xs.foldr (fun x s => (x+s)%p) 0

theorem canonicalSum_eq (xs : List Nat) : canonicalSum xs = xs.sum % p := by
  induction xs with
  | nil => simp [canonicalSum]
  | cons x xs ih =>
      simp only [canonicalSum,List.foldr_cons,List.sum_cons] at *
      rw [ih]
      simp [Nat.add_mod]

theorem reorder_preserves (xs ys : List Nat) (h : xs.Perm ys) :
    canonicalSum xs = canonicalSum ys := by
  rw [canonicalSum_eq,canonicalSum_eq,h.sum_eq]

theorem word_sum_bound (xs : List Nat) (h : ∀ x ∈ xs, x < 2^32) :
    xs.sum ≤ xs.length * (2^32-1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun v hv => h v (List.mem_cons_of_mem x hv))
      simp only [List.sum_cons,List.length_cons]
      omega

theorem accumulator_fits (xs : List Nat) (hlen : xs.length ≤ 272)
    (h : ∀ x ∈ xs, x < 2^32) : xs.sum < 2^41 ∧ xs.sum < 2^64 := by
  have hs := word_sum_bound xs h
  omega

theorem every_prefix_fits (xs ys : List Nat) (hlen : (xs++ys).length ≤ 272)
    (h : ∀ x ∈ xs++ys, x < 2^32) : xs.sum < 2^64 := by
  have hs := accumulator_fits (xs++ys) hlen h
  simp only [List.sum_append] at hs
  omega

theorem binary_selection (b : Bool) (x : Nat) :
    (if b then x else 0) = x * (if b then 1 else 0) := by
  cases b <;> simp

#print axioms canonicalSum_eq
#print axioms reorder_preserves
#print axioms word_sum_bound
#print axioms accumulator_fits
#print axioms every_prefix_fits
#print axioms binary_selection
end AspisV8R19.SelectorGather
