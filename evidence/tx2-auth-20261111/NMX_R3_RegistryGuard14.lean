import NMX_R3_RegistryReadonly
import NMX_R3_RegistryFlagValues
import NMX_R3_RegistryRecordGuards
import NMX_R3_RegistryScriptParts
import NMX_R3_RegistryPure
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryGuard14
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws

attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp : solana_pubkey.Pubkey)
 (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) (expected : solana_pubkey.Pubkey) :
 eval (NMX_R3_RegistryScriptParts.script014 (NMX_R3_RegistryOps.install base D env)
  v s reg ent t m.key rp r expected) =
 (if !decide (reg.key = expected) || NMX_R3_RegistryRecordGuards.bad1 m s r
  then RSL.Spec.pure (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)
  else eval (NMX_R3_RegistryReadonly.call (NMX_R3_RegistryOps.install base D env) ent rp
   (NMX_R3_RegistryScriptParts.script015 (NMX_R3_RegistryOps.install base D env) v ent t m.key rp))) := by
 simp only [NMX_R3_RegistryScriptParts.script014,NMX_R3_RegistryReadonly.call,
  NMX_R3_RegistryProtocols.tryTail,eval_bind,eval_scalar,eval_if,eval_pure,
  NMX_R3_RegistryStd.key_ne,NMX_R3_RegistryScalarOps.to_bytes,
  NMX_R3_RegistryFlagValues.paused1,NMX_R3_RegistryFlagValues.immutable1,
  NGL_ArrayEquality.ne_value,r1_pool_adapter.owned.OwnedAccount.impl.key,
  NMX_R3_RegistryPure.ok,RSL.Spec.bind_pure,NMX_R3_RegistryRecordGuards.bad1,
  NND_BoolReject.not_guard]
 exact NND_BoolReject.six _ _ _ _ _ _ _ _
#print axioms source
end NMX_R3_RegistryGuard14
end
