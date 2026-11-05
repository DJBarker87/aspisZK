import Lean
import NHC_NGG_SpineRef.Types

set_option autoImplicit false
open Aeneas Aeneas.Std
namespace NHC_NGG_ErrorImage
/-- Model of the request helper's constant error map; no native frame claim. -/
def request {R E : Type} (reply : core.result.Result R E) : core.result.Result R NHC_NGG_SpineRef.NGGSpineError :=
 match reply with | .Err _ => .Err .InvalidInstructionData | .Ok r => .Ok r

theorem failure {R E : Type} (reply : core.result.Result R E) (error : NHC_NGG_SpineRef.NGGSpineError)
    (failed : request reply = .Err error) : error = .InvalidInstructionData := by
 cases reply <;> simp_all [request]
#print axioms failure

theorem success {R E : Type} (reply : core.result.Result R E) (value : R)
    (accepted : request reply = .Ok value) : reply = .Ok value := by
 cases reply <;> simp_all [request]
#print axioms success
end NHC_NGG_ErrorImage

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
