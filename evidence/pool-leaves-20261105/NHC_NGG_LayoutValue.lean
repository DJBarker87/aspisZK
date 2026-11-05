import Lean
import NHC_NGG_LayoutGTransfer
import NHC_NGG_LayoutGWithdrawal
import NHC_NGG_LayoutRTransfer
import NHC_NGG_LayoutRWithdrawal

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_NGG_LayoutValue
open NHC_NGG_SpineRef
theorem result (rollover withdrawal : Bool) (n : Usize)
    (unique : core.result.Result Unit NGGSpineError) :
    NHC_NGG_SpineRef.layout_tail (cursor rollover) withdrawal n unique =
      ok (value rollover withdrawal n unique) := by
  cases rollover <;> cases withdrawal
  · exact NHC_NGG_LayoutGTransfer.result n unique
  · exact NHC_NGG_LayoutGWithdrawal.result n unique
  · exact NHC_NGG_LayoutRTransfer.result n unique
  · exact NHC_NGG_LayoutRWithdrawal.result n unique
#print axioms result
end NHC_NGG_LayoutValue

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
