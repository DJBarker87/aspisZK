import NNH_MRegistryArgs
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryRecordGuards
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_CompareTransport NNH_ModelCarrier
open aspis_statement.pool_v1.verifier_registry
attribute [local instance] Classical.propDecidable

def bad1 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (r : VerifierRegistryV1) : Bool :=
 !decide (r.pool = m.key) || !decide (r.authority = s.verifier_policy.registry_authority)
 || !decide (r.policy_binding = s.verifier_policy.policy_binding)
 || !(r.flags &&& 2#u8 != 0#u8) || (r.flags &&& 1#u8 != 0#u8)

theorem registry1 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (reg : VerifierRegistryV1) :
 bad1 m s reg = RSL.TX2_234.registryV1Bad (NNH_MRegistryArgs.args v p m s r e t) (registryV1 reg) := by
 unfold bad1 RSL.TX2_234.registryV1Bad NNH_MRegistryArgs.args account master policy registryV1
 simp only [key_ne,NND_Carrier.flags,RSL.RegistryV1.is_immutable,RSL.RegistryV1.is_paused,
  RSL.REGISTRY_FLAG_IMMUTABLE,RSL.REGISTRY_FLAG_PAUSED]
 rfl

def bad2 (D : RSL.DeployedIds) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r : VerifierRegistryV2) (rpd : solana_pubkey.Pubkey) : Bool :=
 !decide (r.pool = m.key) || !decide (r.authority = s.verifier_policy.registry_authority)
 || !decide (r.policy_binding = s.verifier_policy.policy_binding)
 || !decide (r.registry_program = unkey D.registry) || !decide (r.loader_program = unkey RSL.LOADER_ID)
 || !decide (r.programdata_address = rpd)
 || !(r.flags &&& 2#u8 != 0#u8) || (r.flags &&& 1#u8 != 0#u8)

theorem registry2 (D : RSL.DeployedIds) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : VerifierRegistryV2) (rpd : solana_pubkey.Pubkey) :
 bad2 D m s reg rpd = RSL.TX2_234.registryV2Bad D (NNH_MRegistryArgs.args v p m s r e t)
  (registryV2 reg) (key rpd) := by
 unfold bad2 RSL.TX2_234.registryV2Bad NNH_MRegistryArgs.args account master policy registryV2
 simp only [key_ne,NND_Carrier.flags,key_forth,RSL.RegistryV2.is_immutable,RSL.RegistryV2.is_paused,
  RSL.REGISTRY_FLAG_IMMUTABLE,RSL.REGISTRY_FLAG_PAUSED]
 rfl

#print axioms registry1
#print axioms registry2
end NNH_MRegistryRecordGuards
end
