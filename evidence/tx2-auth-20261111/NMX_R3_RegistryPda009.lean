import NMX_R3_RegistryProtocols
import NMX_R3_RegistryPdaLaw
import NMX_R3_RegistryPure
import NMX_R3_PdaSeeds
import NMX_R3_RegistryScalarOps
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPda009
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (registry_program : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 eval (NMX_R3_RegistryScriptParts.script009 (NMX_R3_RegistryOps.install base D env) verifier_program entry_account current_slot a6 loader p registry_program val5) =
 RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.entry2 p val5.bump) registry_program) (NMX_R3_RegistryPdaLaw.next (fun val6 => eval (NMX_R3_RegistryScriptParts.script010 (NMX_R3_RegistryOps.install base D env) verifier_program entry_account current_slot a6 loader p val5 val6))) := by
 simp only [NMX_R3_RegistryScriptParts.script009,eval_bind,eval_scalar,eval_pda,
  NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure]
 apply congrArg (RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.entry2 p val5.bump) registry_program))
 funext r
 change eval (NMX_R3_RegistryProtocols.formatTail r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () r (fun val6 => NMX_R3_RegistryScriptParts.script010 (NMX_R3_RegistryOps.install base D env) verifier_program entry_account current_slot a6 loader p val5 val6)) = _
 cases r with
 | Ok a =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Ok a) (fun val6 => NMX_R3_RegistryScriptParts.script010 (NMX_R3_RegistryOps.install base D env) verifier_program entry_account current_slot a6 loader p val5 val6)
 | Err e =>
  exact NMX_R3_RegistryProtocols.eval_format
    r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_5.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Err e) (fun val6 => NMX_R3_RegistryScriptParts.script010 (NMX_R3_RegistryOps.install base D env) verifier_program entry_account current_slot a6 loader p val5 val6)
#print axioms source
end NMX_R3_RegistryPda009
end
