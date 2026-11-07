import NMX_R3_RegistryProtocols
import NMX_R3_RegistryPdaLaw
import NMX_R3_RegistryPure
import NMX_R3_PdaSeeds
import NMX_R3_RegistryScalarOps
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPda013
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (verifier_program : solana_pubkey.Pubkey) (master_account : r1_pool_adapter.owned.OwnedAccount) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (registry_account : r1_pool_adapter.owned.OwnedAccount) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (registry_program : Array U8 32#usize) (val1 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
 eval (NMX_R3_RegistryScriptParts.script013 (NMX_R3_RegistryOps.install base D env) verifier_program master_account master registry_account entry_account current_slot registry_program val1) =
 RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.registry1 master_account.key val1.bump) registry_program) (NMX_R3_RegistryPdaLaw.next (fun val2 => eval (NMX_R3_RegistryScriptParts.script014 (NMX_R3_RegistryOps.install base D env) verifier_program master registry_account entry_account current_slot master_account.key registry_program val1 val2))) := by
 simp only [NMX_R3_RegistryScriptParts.script013,eval_bind,eval_scalar,eval_pda,
  NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure]
 apply congrArg (RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.registry1 master_account.key val1.bump) registry_program))
 funext r
 change eval (NMX_R3_RegistryProtocols.formatTail r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_8.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () r (fun val2 => NMX_R3_RegistryScriptParts.script014 (NMX_R3_RegistryOps.install base D env) verifier_program master registry_account entry_account current_slot master_account.key registry_program val1 val2)) = _
 cases r with
 | Ok a =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_8.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Ok a) (fun val2 => NMX_R3_RegistryScriptParts.script014 (NMX_R3_RegistryOps.install base D env) verifier_program master registry_account entry_account current_slot master_account.key registry_program val1 val2)
 | Err e =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_8.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Err e) (fun val2 => NMX_R3_RegistryScriptParts.script014 (NMX_R3_RegistryOps.install base D env) verifier_program master registry_account entry_account current_slot master_account.key registry_program val1 val2)
#print axioms source
end NMX_R3_RegistryPda013
end
