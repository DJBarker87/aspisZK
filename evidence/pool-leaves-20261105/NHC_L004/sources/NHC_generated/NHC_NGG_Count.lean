import Lean
import NHC_NGG_Ref.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_NGG_Count
/-- Full Result, without any bound on actual or expected length. -/
theorem result (actual expected : Usize) :
    NHC_NGG_Ref.count actual expected = ok (if actual != expected then
      if actual < expected then .Err NHC_NGG_Ref.Error.NotEnoughAccountKeys
      else .Err NHC_NGG_Ref.Error.InvalidArgument else .Ok ()) := by
  unfold NHC_NGG_Ref.count
  split_ifs <;> rfl
#print axioms result
end NHC_NGG_Count

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
