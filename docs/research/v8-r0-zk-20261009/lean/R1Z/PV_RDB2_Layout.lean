import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! A value-level transport for the changed `Layout::repeat` calculation.
The parameter `limit` combines the word/product and layout bounds. This is
not a proof of pointer, allocator, or compiler semantics. `size` is the
already-padded element size; unpadded layouts are deliberately excluded. -/
namespace R1Z.PV_RDB2_Layout
set_option autoImplicit false

def checked (limit bytes : Nat) : Option Nat :=
  if bytes ≤ limit then some bytes else none

/-- Historical repeat on an already-padded layout: repeat n-1, then extend. -/
def historical (limit size : Nat) : Nat → Option Nat
  | 0 => checked limit 0
  | n+1 => (checked limit (n*size)).bind (fun bytes => checked limit (bytes+size))

/-- Deployed repeat on an already-padded layout: one checked product. -/
def deployed (limit size count : Nat) : Option Nat := checked limit (count*size)

theorem same_result (limit size count : Nat) :
    historical limit size count = deployed limit size count := by
  cases count with
  | zero => simp [historical, deployed]
  | succ n =>
    by_cases h : n*size+size ≤ limit
    · have hp : n*size ≤ limit := by omega
      simp [historical, deployed, checked, Nat.add_mul, hp, h]
    · by_cases hp : n*size ≤ limit
      · simp [historical, deployed, checked, Nat.add_mul, hp, h]
      · simp [historical, deployed, checked, Nat.add_mul, hp, h]

/-- The allocation layout error is preserved as well as the successful size. -/
theorem same_failure (limit size count : Nat) :
    historical limit size count = none ↔ deployed limit size count = none := by
  rw [same_result]

#print axioms same_result
#print axioms same_failure
end R1Z.PV_RDB2_Layout
