import NMX_R3_ByteCarrier
set_option autoImplicit false
namespace NMX_R3_Constants
open Aeneas Aeneas.Std NMX_R3_ByteCarrier
/-- Fixed 32-byte literal, checked independently of any decoder recurrence. -/
theorem binding : NCV_Reference.BINDING.val.map byte = RSL.FORMAT_BINDING := by
 unfold NCV_Reference.BINDING RSL.FORMAT_BINDING
 rfl
/-- Fixed 21-by-8 literal table, with no recurrence or field arithmetic. -/
theorem empty : NCV_Reference.EMPTY.val.map (fun row => row.val.map word) = RSL.EMPTY_ROOTS := by
 unfold NCV_Reference.EMPTY RSL.EMPTY_ROOTS
 rfl
#print axioms binding
#print axioms empty
end NMX_R3_Constants
