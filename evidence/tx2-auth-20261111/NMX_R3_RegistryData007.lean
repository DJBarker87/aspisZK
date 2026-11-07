import NMX_R3_RegistryProtocols
import NMX_R3_RegistryDataLaw
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryData007
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem source (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) :
 eval (NMX_R3_RegistryScriptParts.script007 ops verifier_program entry_account current_slot a6 loader p registry_program) =
 RSL.Spec.bind (dataSpec entry_account) (NMX_R3_RegistryDataLaw.next (fun val4 => eval (NMX_R3_RegistryScriptParts.script008 ops verifier_program entry_account current_slot a6 loader p registry_program val4))) := by
 simp only [NMX_R3_RegistryScriptParts.script007,eval_bind,eval_data,eval_scalar]
 apply congrArg (RSL.Spec.bind (dataSpec entry_account))
 funext r
 change eval (NMX_R3_RegistryProtocols.tryTail r (fun val4 => NMX_R3_RegistryScriptParts.script008 ops verifier_program entry_account current_slot a6 loader p registry_program val4)) = _
 cases r with
 | Ok a =>
  exact NMX_R3_RegistryProtocols.eval_try (.Ok a) (fun val4 => NMX_R3_RegistryScriptParts.script008 ops verifier_program entry_account current_slot a6 loader p registry_program val4)
 | Err e =>
  exact NMX_R3_RegistryProtocols.eval_try (.Err e) (fun val4 => NMX_R3_RegistryScriptParts.script008 ops verifier_program entry_account current_slot a6 loader p registry_program val4)
#print axioms source
end NMX_R3_RegistryData007
end
