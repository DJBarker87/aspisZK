import NND_RegistryLibrary
import NND_MasterCarrier
import NND_Constants
import NND_CompareTransport
set_option autoImplicit false
noncomputable section
namespace NND_RegistryArgs
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_CompareTransport
attribute [local instance] Classical.propDecidable

def args (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) : RSL.TX2_234.Args :=
 ⟨key v,key p,account m,NND_Carrier.master s,account r,account e,slot t⟩

def policyBad (D : RSL.DeployedIds) (p : solana_pubkey.Pubkey)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) : Bool :=
 !decide (p = unkey D.pool)
 || decide (s.verifier_policy.flags &&& 1#u8 = 0#u8)
 || !decide (s.verifier_policy.registry_program = unkey D.registry)
 || !decide (s.verifier_policy.registry_authority = Array.repeat 32#usize 0#u8)
 || !decide (s.verifier_policy.policy_binding = r1_pool_adapter.AUDIT_POLICY_BINDING)

theorem policy_bad (D : RSL.DeployedIds) (v p : solana_pubkey.Pubkey)
 (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 policyBad D p s = RSL.TX2_234.policyBad D (args v p m s r e t) := by
 unfold policyBad RSL.TX2_234.policyBad args NND_Carrier.master NND_Carrier.policy
 simp only [key_ne,flag_clear,key_forth,NND_Constants.zero_key,NND_Constants.audit,
  RSL.POLICY_FLAG_IMMUTABLE_REGISTRY]
 rfl

#print axioms policy_bad
end NND_RegistryArgs
end
