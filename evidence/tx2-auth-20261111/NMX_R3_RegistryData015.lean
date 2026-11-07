import NMX_R3_RegistryProtocols
import NMX_R3_RegistryDataLaw
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryData015
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem source (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) :
 eval (NMX_R3_RegistryScriptParts.script015 ops verifier_program entry_account current_slot p registry_program) =
 RSL.Spec.bind (dataSpec entry_account) (NMX_R3_RegistryDataLaw.next (fun val3 => eval (NMX_R3_RegistryScriptParts.script016 ops verifier_program entry_account current_slot p registry_program val3))) := by
 simp only [NMX_R3_RegistryScriptParts.script015,eval_bind,eval_data,eval_scalar]
 apply congrArg (RSL.Spec.bind (dataSpec entry_account))
 funext r
 change eval (NMX_R3_RegistryProtocols.tryTail r (fun val3 => NMX_R3_RegistryScriptParts.script016 ops verifier_program entry_account current_slot p registry_program val3)) = _
 cases r with
 | Ok a =>
  exact NMX_R3_RegistryProtocols.eval_try (.Ok a) (fun val3 => NMX_R3_RegistryScriptParts.script016 ops verifier_program entry_account current_slot p registry_program val3)
 | Err e =>
  exact NMX_R3_RegistryProtocols.eval_try (.Err e) (fun val3 => NMX_R3_RegistryScriptParts.script016 ops verifier_program entry_account current_slot p registry_program val3)
#print axioms source
end NMX_R3_RegistryData015
end
