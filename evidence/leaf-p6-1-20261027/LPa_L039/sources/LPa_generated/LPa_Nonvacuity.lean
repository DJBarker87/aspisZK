import LPa_Check
import LPa_Echeck
import LPa_Validate
import LPa_Expand
open Aeneas Aeneas.Std Result
open XRk_Release
set_option autoImplicit false
namespace LPa.Nonvacuity
def empty : Slice U8 := ⟨[],by decide⟩

theorem check_accepts : compact.check_values empty = ok (.Ok ()) := by rfl
theorem echeck_accepts (k : Bool) : verifier.echeck empty k = ok (.Ok ()) := by rfl
theorem validate_accepts (row : U8) : r1_wire.validate_record_fields row empty = ok (.Ok ()) := by rfl
-- This is the exact modeled error result, not a vacuous successful-return antecedent.
theorem invalid_row_reached :
    r1_wire.ValidatedRecord.decode_k 29#usize ⟨0#u8,empty⟩ 0#usize = ok (.Err .InvalidRow) := by rfl

#print axioms check_accepts
#print axioms echeck_accepts
#print axioms validate_accepts
#print axioms invalid_row_reached
end LPa.Nonvacuity
