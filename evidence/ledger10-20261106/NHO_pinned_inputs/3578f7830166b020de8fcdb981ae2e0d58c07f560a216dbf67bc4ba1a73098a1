import NGG_SpineRef.Types
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace NGG_ErrorImage
/-- Model of the request helper's constant error map; no native frame claim. -/
def request {R E : Type} (reply : core.result.Result R E) : core.result.Result R NGG_SpineRef.NGGSpineError :=
 match reply with | .Err _ => .Err .InvalidInstructionData | .Ok r => .Ok r

theorem failure {R E : Type} (reply : core.result.Result R E) (error : NGG_SpineRef.NGGSpineError)
    (failed : request reply = .Err error) : error = .InvalidInstructionData := by
 cases reply <;> simp_all [request]
#print axioms failure

theorem success {R E : Type} (reply : core.result.Result R E) (value : R)
    (accepted : request reply = .Ok value) : reply = .Ok value := by
 cases reply <;> simp_all [request]
#print axioms success
end NGG_ErrorImage
