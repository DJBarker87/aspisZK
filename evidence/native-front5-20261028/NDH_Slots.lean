import NDH_Reference.Funs
import Port4B_SlotInstall
set_option autoImplicit false
noncomputable section
namespace NDH_Slots
open Aeneas Aeneas.Std Result
open AspisR1.Port4B_SlotInstall
open AspisR1.OraclePortSelectedDraft

theorem reference (slot : Usize) (bound : slot.val ≤ 6) :
    NDH_Reference.slot_ref slot = ok (offset slot.val bound) := by
  have h := bound
  interval_cases v : slot.val <;>
    simp only [NDH_Reference.slot_ref, v, offset, slotStart, capacity] <;> rfl

/-- Every prefix-sum step on the caller's six-slot domain is representable.
This is model induction, with the native single step still separately required. -/
theorem step (slot : Nat) :
    slotStart (slot+1) = slotStart slot + 32 * capacity slot := offset_step slot

theorem representable (slot : Nat) (bound : slot ≤ 6) :
    (offset slot bound).val = slotStart slot := rfl
#print axioms reference
#print axioms step
#print axioms representable
end NDH_Slots
