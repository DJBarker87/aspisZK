import NNH_MRegistry2Guard
import NND_BoolReject
import NNH_MRegistryFlagValues
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2GuardValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2)
 (rpd : solana_pubkey.Pubkey) :
 NNH_MRegistry2Guard.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg rpd =
 if NNH_MRegistryRecordGuards.bad2 D m s reg rpd
 then ok (.Err .InvalidAccountData)
 else NNH_MEntry2Readonly.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) := by
 simp only [NNH_MRegistry2Guard.run,NNH_MRegistryScalarOps.to_bytes,
  NNH_MRegistryFlagValues.paused2,NNH_MRegistryFlagValues.immutable2,
  NGL_ArrayEquality.ne_value,bind_tc_ok,NNH_MRegistryRecordGuards.bad2,NND_BoolReject.not_guard]
 exact NND_BoolReject.eightFlags _ _ _ _ _ _ _ _ _ _

#print axioms value
end NNH_MRegistry2GuardValue
end
