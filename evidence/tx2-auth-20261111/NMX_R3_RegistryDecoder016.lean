import NMX_R3_RegistryProtocols
import NMX_R3_RegistryDecoderLaw
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryDecoder016
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem source (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val3 : Slice U8) :
 eval (NMX_R3_RegistryScriptParts.script016 ops verifier_program entry_account current_slot p registry_program val3) =
 RSL.Spec.bind (scalarSpec (ops.op32 val3)) (NMX_R3_RegistryDecoderLaw.next (fun val4 => eval (NMX_R3_RegistryScriptParts.script017 ops verifier_program entry_account current_slot p registry_program val4))) := by
 simp only [NMX_R3_RegistryScriptParts.script016,eval_bind,eval_scalar]
 apply congrArg (RSL.Spec.bind (scalarSpec (ops.op32 val3)))
 funext r
 change eval (NMX_R3_RegistryProtocols.formatTail r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError () r (fun val4 => NMX_R3_RegistryScriptParts.script017 ops verifier_program entry_account current_slot p registry_program val4)) = _
 cases r with
 | Ok a =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError () (fun _ => rfl) (.Ok a) (fun val4 => NMX_R3_RegistryScriptParts.script017 ops verifier_program entry_account current_slot p registry_program val4)
 | Err e =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_9.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError () (fun _ => rfl) (.Err e) (fun val4 => NMX_R3_RegistryScriptParts.script017 ops verifier_program entry_account current_slot p registry_program val4)
#print axioms source
end NMX_R3_RegistryDecoder016
end
