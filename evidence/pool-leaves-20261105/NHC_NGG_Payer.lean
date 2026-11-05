import Lean
import NHC_NGG_Compare

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_NGG_Payer
abbrev Key := NHC_NGG_Compare.Key
theorem result (payer system : NHC_NGG_Ref.Account) (system_id native_id : Key) :
    NHC_NGG_Ref.payer payer system system_id native_id = ok
      (if payer.signer = false ∨ payer.writable = false ∨ payer.executable = true ∨ payer.owner.val ≠ system_id.val
       then .Err NHC_NGG_Ref.Error.InvalidPayer
       else if system.key.val ≠ system_id.val ∨ system.owner.val ≠ native_id.val ∨ system.executable = false ∨ system.signer = true ∨ system.writable = true
       then .Err NHC_NGG_Ref.Error.InvalidSystemProgram else .Ok ()) := by
  simp only [NHC_NGG_Ref.payer,NHC_NGG_Compare.ne,bind_tc_ok]
  split_ifs <;> simp_all
#print axioms result
end NHC_NGG_Payer

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
