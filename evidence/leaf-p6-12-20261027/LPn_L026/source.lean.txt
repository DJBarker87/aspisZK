import LPl_EcheckResult
import AspisR1FinishRelationCurrent.Types
set_option autoImplicit false
namespace LPl
/-- Co-import audit of the original collision class. -/
theorem coimport_identity (x : LPl_Kit_Release.verifier.Error) : x = x := rfl
#print axioms coimport_identity
end LPl
