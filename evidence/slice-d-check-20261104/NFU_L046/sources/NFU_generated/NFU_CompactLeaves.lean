import NFQ_COMBINED_IMPORT
import NFU_LPn_ExpandTrace
import NFU_LPl_Check
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open NFU_Retarget
open NFU_Retarget
namespace NFU_CompactLeaves
/-- Import the CLOSED opaque leaf on its exact carrier, preserving rejected
prefixes and the same native trace. There is no accepted-result hypothesis. -/
theorem check_result (bytes : Slice U8) (out : Option Nat)
    (trace : LPl.Scan.Trace (LPl.Check.predicate bytes.val) (bytes.val.length / 16) 0 out) :
    LPl_Kit_Release.compact.check_values bytes =
      ok (if out.isNone then .Ok () else .Err .NonCanonical) :=
  LPl.Check.native_result bytes out trace

/-- The existing spatial induction composes the KMX-revalidated local window;
the trace contains only per-step observations, not a final-output equality. -/
theorem expand_result (bytes before after : Slice U8)
    (bound : bytes.val.length ≤ 1856) (aligned : bytes.val.length % 16 = 0)
    (shape : before.val.length = 2 * bytes.val.length)
    (trace : LPn.Expand.NativeTrace bytes.val before.val (bytes.val.length / 16) after.val) :
    LPl_Kit_Release.compact.expand_values bytes before = ok (.Ok (),after) :=
  LPn.Expand.native_result bytes before after bound aligned shape trace

theorem expand_reject (bytes before : Slice U8) (bound : bytes.val.length ≤ 1856)
    (bad : bytes.val.length % 16 ≠ 0 ∨ before.val.length ≠ 2 * bytes.val.length) :
    LPl_Kit_Release.compact.expand_values bytes before = ok (.Err .Length,before) :=
  LPn.Expand.length_error bytes before bound bad
#print axioms check_result
#print axioms expand_result
#print axioms expand_reject
end NFU_CompactLeaves
