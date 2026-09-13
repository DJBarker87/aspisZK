import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic

/-!
# K1.3: pre-query and terminal dot products have different lengths

Draft for main 37e1f04b8790f4dc092a38e5ad08d27b00801e0b. NOT kernel checked
in the authoring environment. This module proves facts about explicit finite
sums; it does not purport to prove Rust/Aeneas correspondence.

At the pre-query cut the vector has 256 entries. The four-entry slice belongs
at the terminal cut, after three additional arity-four folds. The pinned
source observer accidentally used the terminal slice at the pre-query cut.

The counterexample is symbolic: it does not enumerate or normalize a
256-element concrete field calculation. It is a local-state counterexample,
not a constructed accepting protocol execution or a soundness attack.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K13SnapshotLengthAudit

open scoped BigOperators

section Scan

variable {R : Type*} [AddMonoid R]

/-- Forward accumulator recurrence, kept symbolic for use in the source-loop
refinement. No claim that this definition is an Aeneas translation is made. -/
def forwardScan (term : Nat → R) : Nat → Nat → R → R
  | _, 0, acc => acc
  | start, count + 1, acc =>
      forwardScan term (start + 1) count (acc + term start)

/-- General loop invariant: an arbitrary incoming accumulator contributes
exactly once. This avoids normalizing a 256-step generated recurrence. -/
theorem forwardScan_eq_acc_add_zero (term : Nat → R)
    (start count : Nat) (acc : R) :
    forwardScan term start count acc =
      acc + forwardScan term start count 0 := by
  induction count generalizing start acc with
  | zero => simp [forwardScan]
  | succ count ih =>
      simp only [forwardScan]
      rw [ih (start + 1) (acc + term start),
        ih (start + 1) (0 + term start)]
      simp only [zero_add, add_assoc]

/-- Splitting a scan does not change its order or duplicate the initial sum. -/
theorem forwardScan_split (term : Nat → R)
    (start left right : Nat) (acc : R) :
    forwardScan term start (left + right) acc =
      forwardScan term (start + left) right
        (forwardScan term start left acc) := by
  induction left generalizing start acc with
  | zero => simp [forwardScan]
  | succ left ih =>
      simpa only [Nat.succ_add, forwardScan, Nat.add_succ,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start + 1) (acc + term start)

end Scan

section PrefixInvariant

variable {R : Type*} [AddCommMonoid R]

/-- The source-style accumulator invariant at an arbitrary starting index. -/
theorem forwardScan_prefix_sum (term : Nat → R) (start count : Nat) :
    forwardScan term start count (∑ i ∈ Finset.range start, term i) =
      ∑ i ∈ Finset.range (start + count), term i := by
  induction count generalizing start with
  | zero => simp [forwardScan]
  | succ count ih =>
      rw [forwardScan, ← Finset.sum_range_succ]
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start + 1)

/-- The generic dot-loop recurrence computes the complete prefix sum. -/
theorem forwardScan_zero_eq_sum (term : Nat → R) (count : Nat) :
    forwardScan term 0 count 0 = ∑ i ∈ Finset.range count, term i := by
  simpa using forwardScan_prefix_sum term 0 count

end PrefixInvariant

section FiniteDot

variable {R : Type*} [Semiring R]

/-- The generic dot branch with only the first `count` values supplied.
The multiplication order agrees with WeightAccumulator::dot. -/
def dotThrough (count : Nat) (weights values : Fin 256 → R) : R :=
  ∑ i, if i.val < count then values i * weights i else 0

/-- Reading all entries is exactly the maintained full finite dot product. -/
theorem dotThrough_256 (weights values : Fin 256 → R) :
    dotThrough 256 weights values = ∑ i, values i * weights i := by
  unfold dotThrough
  apply Finset.sum_congr rfl
  intro i _
  exact if_pos i.isLt

/-- The omitted contribution is explicit; it must not be silently set to zero. -/
theorem dotThrough_add_omitted (count : Nat)
    (weights values : Fin 256 → R) :
    dotThrough count weights values +
        (∑ i : Fin 256, if count ≤ i.val then values i * weights i else 0) =
      ∑ i : Fin 256, values i * weights i := by
  unfold dotThrough
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val < count
  · simp [h, Nat.not_le_of_lt h]
  · simp [h, Nat.le_of_not_gt h]

/-- A single nonzero entry immediately outside the incorrect four-entry slice. -/
def spikeAtFour : Fin 256 → R :=
  fun i => if i.val = 4 then 1 else 0

/-- The incorrect slice entirely misses the fifth coefficient. -/
theorem dotThrough_four_spike :
    dotThrough 4 (fun _ => (1 : R)) spikeAtFour = 0 := by
  classical
  unfold dotThrough
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i.val = 4 <;> simp [spikeAtFour, h]

/-- The full pre-query vector includes that coefficient exactly once. -/
theorem dotThrough_256_spike :
    dotThrough 256 (fun _ => (1 : R)) spikeAtFour = 1 := by
  classical
  rw [dotThrough_256]
  simp only [mul_one]
  rw [Finset.sum_eq_single (4 : Fin 256)]
  · simp [spikeAtFour]
  · intro i _ hi
    by_cases h : i.val = 4
    · exact False.elim (hi (Fin.ext h))
    · simp [spikeAtFour, h]
  · simp

/-- Thus a universal four-entry-to-256-entry source bridge is false. -/
theorem four_entry_dot_is_not_full_dot [Nontrivial R] :
    dotThrough 4 (fun _ => (1 : R)) spikeAtFour ≠
      dotThrough 256 (fun _ => (1 : R)) spikeAtFour := by
  rw [dotThrough_four_spike, dotThrough_256_spike]
  exact zero_ne_one

end FiniteDot

#print axioms forwardScan_eq_acc_add_zero
#print axioms forwardScan_split
#print axioms forwardScan_prefix_sum
#print axioms forwardScan_zero_eq_sum
#print axioms dotThrough_256
#print axioms dotThrough_add_omitted
#print axioms four_entry_dot_is_not_full_dot

end AspisK1.V7Tag73K13SnapshotLengthAudit
