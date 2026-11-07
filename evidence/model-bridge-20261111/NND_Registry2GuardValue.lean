import NND_Registry2Guard
import NND_BoolReject
import NND_RegistryFlagValues
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NND_Registry2GuardValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2)
 (rpd : solana_pubkey.Pubkey) :
 NND_Registry2Guard.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg rpd =
 if NND_RegistryRecordGuards.bad2 D m s reg rpd
 then ok (.Err .InvalidAccountData)
 else NND_Entry2Readonly.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) := by
 simp only [NND_Registry2Guard.run,NND_RegistryScalarOps.to_bytes,
  NND_RegistryFlagValues.paused2,NND_RegistryFlagValues.immutable2,
  NGL_ArrayEquality.ne_value,bind_tc_ok,NND_RegistryRecordGuards.bad2,NND_BoolReject.not_guard]
 exact NND_BoolReject.eightFlags _ _ _ _ _ _ _ _ _ _

#print axioms value
end NND_Registry2GuardValue
end
