import NNH_MRegistryEntry2Value
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry2ValueRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
 (vpd : solana_pubkey.Pubkey) :
 outer (reply id) (NNH_MRegistryEntry2Check.check (NNH_MRegistryOps.install base D env) v m.key t (unkey RSL.LOADER_ID) entry vpd) =
 ok (eseq (echeck (RSL.TX2_234.entryV2Bad (NNH_MRegistryArgs.args v p m s r e t) (entryV2 entry) (key vpd)) .invalidAccountData) (.ok ())) := by
 rw [NNH_MRegistryEntry2Value.value,NNH_MEntryV2Guard.value v p m s r e t]
 cases h : RSL.TX2_234.entryV2Bad (NNH_MRegistryArgs.args v p m s r e t) (entryV2 entry) (key vpd) <;> rfl

#print axioms value
end NNH_MEntry2ValueRSL
end
