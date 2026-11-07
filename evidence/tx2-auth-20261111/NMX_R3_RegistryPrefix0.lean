import NMX_R3_RegistryProtocols
import NMX_R3_RegistryScalarOps
import NMX_R3_RegistryArgs
import NMX_R3_RegistryPure
import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryBoolFive
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPrefix0
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
attribute [local instance] Classical.propDecidable

def policyTail (ops : Ops) (a : aspis_statement.pool_v1.format.VerifierPolicyV1)
 (next : Program (core.result.Result Unit solana_program_error.ProgramError)) := do
 let r ← scalar (ops.op15 a)
 NMX_R3_RegistryProtocols.formatTail
  r1_pool_adapter.owned.authenticate_invariant_release_registry.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1FormatErrorProgramError
  () r (fun _ => next)

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 eval (NMX_R3_RegistryScriptParts.script000 (NMX_R3_RegistryOps.install base D env) v p m s reg ent t) =
 (if NMX_R3_RegistryArgs.policyBad D p s then
   RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)
  else eval (policyTail (NMX_R3_RegistryOps.install base D env) s.verifier_policy
   (NMX_R3_RegistryScriptParts.script001 (NMX_R3_RegistryOps.install base D env) v m s reg ent t (unkey D.registry)))) := by
 simp only [NMX_R3_RegistryScriptParts.script000,policyTail,
  NMX_R3_RegistryProtocols.formatTail,NMX_R3_RegistryProtocols.tryTail,
  eval_bind,eval_scalar,eval_if,eval_pure,NMX_R3_RegistryScalarOps.to_bytes,
  NMX_R3_RegistryScalarOps.pool,NMX_R3_RegistryScalarOps.registry,
  NMX_R3_RegistryScalarOps.immutable_flag,NGL_ArrayEquality.ne_value,
  Aeneas.Std.lift,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,NMX_R3_RegistryArgs.policyBad]
 exact NMX_R3_RegistryBoolFive.fold _ _ _ _ _ _ _
#print axioms source
end NMX_R3_RegistryPrefix0
end
