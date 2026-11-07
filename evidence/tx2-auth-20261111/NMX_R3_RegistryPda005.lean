import NMX_R3_RegistryProtocols
import NMX_R3_RegistryPdaLaw
import NMX_R3_RegistryPure
import NMX_R3_PdaSeeds
import NMX_R3_RegistryScalarOps
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPda005
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (verifier_program : solana_pubkey.Pubkey) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (val2 : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script005 (NMX_R3_RegistryOps.install base D env) verifier_program master registry_account entry_account current_slot loader p registry_program val1 val2) =
 (if !decide (registry_account.key = val2) then RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData) else
 RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.programdata registry_program val1.programdata_bump) loader) (NMX_R3_RegistryPdaLaw.next (fun val3 => eval (NMX_R3_RegistryScriptParts.script006 (NMX_R3_RegistryOps.install base D env) verifier_program master entry_account current_slot loader p registry_program val1 val3)))) := by
 by_cases rejected : (!decide (registry_account.key = val2)) = true
 · simp only [NMX_R3_RegistryScriptParts.script005,eval_bind,eval_scalar,eval_pda,eval_if,eval_pure,
   NMX_R3_RegistryStd.key_ne,NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,rejected,↓reduceIte]
 · simp only [NMX_R3_RegistryScriptParts.script005,eval_bind,eval_scalar,eval_pda,eval_if,eval_pure,
   NMX_R3_RegistryStd.key_ne,NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,rejected,↓reduceIte]
   apply congrArg (RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.programdata registry_program val1.programdata_bump) loader))
   funext r
   change eval (NMX_R3_RegistryProtocols.formatTail r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () r (fun val3 => NMX_R3_RegistryScriptParts.script006 (NMX_R3_RegistryOps.install base D env) verifier_program master entry_account current_slot loader p registry_program val1 val3)) = _
   cases r with
   | Ok a =>
    exact NMX_R3_RegistryProtocols.eval_format
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Ok a) (fun val3 => NMX_R3_RegistryScriptParts.script006 (NMX_R3_RegistryOps.install base D env) verifier_program master entry_account current_slot loader p registry_program val1 val3)
   | Err e =>
    exact NMX_R3_RegistryProtocols.eval_format
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_3.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Err e) (fun val3 => NMX_R3_RegistryScriptParts.script006 (NMX_R3_RegistryOps.install base D env) verifier_program master entry_account current_slot loader p registry_program val1 val3)
#print axioms source
end NMX_R3_RegistryPda005
end
