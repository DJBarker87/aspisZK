import PV_B3P_Std559Types227
namespace PV_B3P_StringBound559227
open Aeneas Aeneas.Std
set_option autoImplicit false
/-- Fixed diagnostic string bound, checked in the kernel after exposing the
String byte-size theorem, rather than invoking the toStr default proof tactic. -/
theorem step_message_bound : "`Step` invariants not upheld".toByteArray.size ≤ U32.max := by
  simp only [String.size_toByteArray,U32.max_eq]
  decide
#print axioms step_message_bound
end PV_B3P_StringBound559227
