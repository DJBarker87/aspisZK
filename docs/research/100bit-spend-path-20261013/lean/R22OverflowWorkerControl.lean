import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! New, distinctly named worker module. Source-shaped integer ranges only;
no Rust/extraction correspondence or endpoint premise deletion is claimed. -/
set_option autoImplicit false
namespace AspisR1.R22OverflowWorkerControl

/-- The packed pair is a + 2^32*b; canonical lanes bound every ordered add,
including both reduce_pair additions. OR/shift correspondence is checked by
Kani on the actual copied private methods, separately. -/
theorem packed_add_bounds (a b c d : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647)
    (hc : c < 2147483647) (hd : d < 2147483647) :
    let s := (a + 4294967296*b) + (c + 4294967296*d)
    s < 18446744073709551616 ∧
    s + 4294967297 < 18446744073709551616 ∧
    s + 4294967297 + 4294967297 < 18446744073709551616 := by
  dsimp only
  omega

/-- Packed subtraction is offset before subtraction, so no saturated Nat
subtraction conceals a machine underflow. -/
theorem packed_sub_bounds (a b c d : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647)
    (hc : c < 2147483647) (hd : d < 2147483647) :
    let left := a + 4294967296*b + 9223372034707292159
    let right := c + 4294967296*d
    right ≤ left ∧ left < 18446744073709551616 ∧
    left-right + 4294967297 + 4294967297 < 18446744073709551616 := by
  dsimp only
  omega

/-- Overapproximate the frontier loops by a list of sibling increments.
At most 18 levels * 16 parent groups, at most eight siblings per group.
This also covers ordinary rejecting reads, before their byte-length check. -/
theorem sibling_sum (steps : List Nat) (h : ∀ x ∈ steps, x ≤ 8) :
    steps.sum ≤ 8 * steps.length := by
  induction steps with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs : ∀ y ∈ xs, y ≤ 8 := by
      intro y hy
      exact h y (by simp [hy])
    have hi := ih hs
    simp only [List.sum_cons, List.length_cons]
    omega

theorem sibling_cursor (steps : List Nat) (h : ∀ x ∈ steps, x ≤ 8)
    (hlen : steps.length ≤ 288) :
    steps.sum ≤ 2304 ∧ 32 * steps.sum + 32 ≤ 73760 ∧
    32 * steps.sum + 32 < 4294967296 := by
  have hs := sibling_sum steps h
  omega

/-- A binary body consumes one or two inputs and writes one output.
The decrease and write bounds are sufficient for an independent loop proof. -/
theorem binary_progress (i n w consumed : Nat)
    (hn : n ≤ 16) (hi : i < n) (hw : w ≤ i)
    (hc : consumed = 1 ∨ consumed = 2)
    (hp : consumed = 2 → i+1 < n) :
    w < 16 ∧ i+consumed ≤ n ∧ w+1 ≤ i+consumed ∧
    n-(i+consumed) < n-i ∧ w+1 ≤ 16 := by
  rcases hc with h | h <;> omega

/-- Inner node_count group: a nonempty group cannot exceed the arity width.
The group-width premise must be derived from strict sorting and parent bits;
it is NOT implied by a generic index bound. -/
theorem group_progress (i j n w count width : Nat)
    (hi : i < j) (hj : j ≤ n) (hn : n ≤ 16) (hw : w ≤ i)
    (hwidth : j-i ≤ width ∧ width ≤ 8) (hcount : count ≤ 2304) :
    width-(j-i) ≤ 8 ∧ count+(width-(j-i)) ≤ 2312 ∧
    w < 16 ∧ w+1 ≤ j ∧ n-j < n-i := by omega

/-- A 16-bit/32-bit field index is not sufficient for a mutable residue lane.
This counterexample prevents erasing the old-lane phase invariant. -/
theorem canonical_product_does_not_bound_old_lane :
    1 < 2147483647 ∧ 1 < 262144 ∧
    ¬ (18446744073709551615 + 1 < 18446744073709551616) := by omega

#print axioms packed_add_bounds
#print axioms packed_sub_bounds
#print axioms sibling_sum
#print axioms sibling_cursor
#print axioms binary_progress
#print axioms group_progress
#print axioms canonical_product_does_not_bound_old_lane
end AspisR1.R22OverflowWorkerControl
