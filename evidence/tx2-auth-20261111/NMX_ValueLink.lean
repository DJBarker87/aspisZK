import NMX_SourceModel
import NMX_EmittedLinks
set_option autoImplicit false
noncomputable section
namespace NMX_ValueLink
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel

def erase : End Unit NLM_Auth233.Event Auth →
 Result (core.result.Result r1_pool_adapter.AuthenticatedAsq8Accounts PE)
 | .returned (.Ok a) _ _ => .ok (.Ok a.erase)
 | .returned (.Err e) _ _ => .ok (.Err e)
 | .stopped _ (.failed e) => .fail e
 | .stopped _ .diverged => .div
/-- Event prefixes do not alter the value projection, even on stops. -/
theorem erase_prepend (es : List NLM_Auth233.Event) (outcome : End Unit NLM_Auth233.Event Auth) :
 erase (prepend es outcome) = erase outcome := by
 cases outcome with
 | stopped events cause => cases cause <;> rfl
 | returned reply post events => cases reply <;> rfl
#print axioms erase_prepend
end NMX_ValueLink
end
