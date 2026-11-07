import NMX_R3_RegistryReadonly
import NMX_R3_RegistryFlagValues
import NMX_R3_RegistryRecordGuards
import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryPure
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryGuard6
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) (rpd : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script006 (NMX_R3_RegistryOps.install base D env)
  v s ent t (unkey RSL.LOADER_ID) m.key (unkey D.registry) r rpd) =
 (if NMX_R3_RegistryRecordGuards.bad2 D m s r rpd
  then RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)
  else eval (NMX_R3_RegistryReadonly.call (NMX_R3_RegistryOps.install base D env) ent (unkey D.registry)
   (NMX_R3_RegistryScriptParts.script007 (NMX_R3_RegistryOps.install base D env)
    v ent t (unkey RSL.LOADER_ID) (unkey RSL.LOADER_ID) m.key (unkey D.registry)))) := by
 simp only [NMX_R3_RegistryScriptParts.script006,NMX_R3_RegistryReadonly.call,
  NMX_R3_RegistryProtocols.tryTail,eval_bind,eval_scalar,eval_if,eval_pure,
  NMX_R3_RegistryScalarOps.to_bytes,
  NMX_R3_RegistryFlagValues.paused2,NMX_R3_RegistryFlagValues.immutable2,
  NGL_ArrayEquality.ne_value,NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,
  NMX_R3_RegistryRecordGuards.bad2,NND_BoolReject.not_guard]
 exact NND_BoolReject.eightFlags _ _ _ _ _ _ _ _ _ _
#print axioms source
end NMX_R3_RegistryGuard6
end
