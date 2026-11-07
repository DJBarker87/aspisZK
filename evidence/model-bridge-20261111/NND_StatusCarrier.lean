import NND_ScalarLaws
import RSL_Pool
set_option autoImplicit false
namespace NND_Carrier
open AdapterRw.aspis_statement.pool_v1.verifier_registry

def status : VerifierEntryStatusV1 → RSL.EntryStatus
 | .Pending => .pending | .Active => .active | .Paused => .paused | .Retired => .retired
def unstatus : RSL.EntryStatus → VerifierEntryStatusV1
 | .pending => .Pending | .active => .Active | .paused => .Paused | .retired => .Retired
@[simp] theorem status_back (x : VerifierEntryStatusV1) : unstatus (status x) = x := by cases x <;> rfl
@[simp] theorem status_forth (x : RSL.EntryStatus) : status (unstatus x) = x := by cases x <;> rfl
#print axioms status_back
#print axioms status_forth
end NND_Carrier
