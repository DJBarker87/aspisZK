import NMX_R3_RegistryProtocols
import NMX_R3_RegistryPdaLaw
import NMX_R3_RegistryPure
import NMX_R3_PdaSeeds
import NMX_R3_RegistryScalarOps
import NMX_R3_RegistryScriptParts
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPda010
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env) (verifier_program : solana_pubkey.Pubkey) (entry_account : r1_pool_adapter.owned.OwnedAccount) (current_slot : U64) (a6 : Array U8 32#usize) (loader : Array U8 32#usize) (p : Array U8 32#usize) (val5 : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) (val6 : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script010 (NMX_R3_RegistryOps.install base D env) verifier_program entry_account current_slot a6 loader p val5 val6) =
 (if !decide (entry_account.key = val6) then RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData) else
 RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.programdata verifier_program val5.programdata_bump) loader) (NMX_R3_RegistryPdaLaw.next (fun val7 => eval (NMX_R3_RegistryScriptParts.script011 (NMX_R3_RegistryOps.install base D env) verifier_program current_slot a6 p val5 val7)))) := by
 by_cases rejected : (!decide (entry_account.key = val6)) = true
 · simp only [NMX_R3_RegistryScriptParts.script010,eval_bind,eval_scalar,eval_pda,eval_if,eval_pure,
   NMX_R3_RegistryStd.key_ne,NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,rejected,↓reduceIte]
 · simp only [NMX_R3_RegistryScriptParts.script010,eval_bind,eval_scalar,eval_pda,eval_if,eval_pure,
   NMX_R3_RegistryStd.key_ne,NMX_R3_RegistryScalarOps.as_ref,r1_pool_adapter.owned.OwnedAccount.impl.key,Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,rejected,↓reduceIte]
   apply congrArg (RSL.Spec.bind (pdaSpec (NMX_R3_PdaSeeds.programdata verifier_program val5.programdata_bump) loader))
   funext r
   change eval (NMX_R3_RegistryProtocols.formatTail r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () r (fun val7 => NMX_R3_RegistryScriptParts.script011 (NMX_R3_RegistryOps.install base D env) verifier_program current_slot a6 p val5 val7)) = _
   cases r with
   | Ok a =>
    exact NMX_R3_RegistryProtocols.eval_format
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Ok a) (fun val7 => NMX_R3_RegistryScriptParts.script011 (NMX_R3_RegistryOps.install base D env) verifier_program current_slot a6 p val5 val7)
   | Err e =>
    exact NMX_R3_RegistryProtocols.eval_format
      r1_pool_adapter.owned.authenticate_invariant_release_registry.closure_6.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError () (fun _ => rfl) (.Err e) (fun val7 => NMX_R3_RegistryScriptParts.script011 (NMX_R3_RegistryOps.install base D env) verifier_program current_slot a6 p val5 val7)
#print axioms source
end NMX_R3_RegistryPda010
end
