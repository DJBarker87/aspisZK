import NND_RegistryEntry2Value
set_option autoImplicit false
noncomputable section
namespace NND_Entry2ValueRSL
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2)
 (vpd : solana_pubkey.Pubkey) :
 outer (reply id) (NND_RegistryEntry2Check.check (NND_RegistryOps.install base D env) v m.key t (unkey RSL.LOADER_ID) entry vpd) =
 ok (eseq (echeck (RSL.TX2_234.entryV2Bad (NND_RegistryArgs.args v p m s r e t) (entryV2 entry) (key vpd)) .invalidAccountData) (.ok ())) := by
 rw [NND_RegistryEntry2Value.value,NND_EntryV2Guard.value v p m s r e t]
 cases h : RSL.TX2_234.entryV2Bad (NND_RegistryArgs.args v p m s r e t) (entryV2 entry) (key vpd) <;> rfl

#print axioms value
end NND_Entry2ValueRSL
end
