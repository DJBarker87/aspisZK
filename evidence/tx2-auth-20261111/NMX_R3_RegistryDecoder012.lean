import NMX_R3_RegistryProtocols
import NMX_R3_RegistryDecoderLaw
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryDecoder012
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem source (ops : Ops) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) (val : Slice U8) :
 eval (NMX_R3_RegistryScriptParts.script012 ops verifier_program master_account master registry_account entry_account current_slot registry_program val) =
 RSL.Spec.bind (scalarSpec (ops.op31 val)) (NMX_R3_RegistryDecoderLaw.next (fun val1 => eval (NMX_R3_RegistryScriptParts.script013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1))) := by
 simp only [NMX_R3_RegistryScriptParts.script012,eval_bind,eval_scalar]
 apply congrArg (RSL.Spec.bind (scalarSpec (ops.op31 val)))
 funext r
 change eval (NMX_R3_RegistryProtocols.formatTail r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_7.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError () r (fun val1 => NMX_R3_RegistryScriptParts.script013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1)) = _
 cases r with
 | Ok a =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_7.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError () (fun _ => rfl) (.Ok a) (fun val1 => NMX_R3_RegistryScriptParts.script013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1)
 | Err e =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_7.Insts.CoreOpsFunctionFnOnceTuplePoolV1VerifierRegistryFormatErrorProgramError () (fun _ => rfl) (.Err e) (fun val1 => NMX_R3_RegistryScriptParts.script013 ops verifier_program master_account master registry_account entry_account current_slot registry_program val1)
#print axioms source
end NMX_R3_RegistryDecoder012
end
