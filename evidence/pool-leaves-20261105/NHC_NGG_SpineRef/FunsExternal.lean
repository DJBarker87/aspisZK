import Lean
import NHC_NGG_SpineRef.Types

open Aeneas Aeneas.Std Result
namespace NHC_NGG_SpineRef
/-- Total option elimination; no external hypothesis. -/
def core.option.Option.ok_or {T E : Type} (x : Option T) (err : E) :
    Result (Aeneas.Std.core.result.Result T E) :=
  ok (match x with | none => .Err err | some value => .Ok value)
end NHC_NGG_SpineRef

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
