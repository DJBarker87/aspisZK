import NND_Registry1Guard
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NND_Registry1GuardValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v rp : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1)
 (expected : solana_pubkey.Pubkey) :
 NND_Registry1Guard.run (NND_RegistryOps.install base D env) v m.key rp s r e t reg expected =
 if !decide (r.key = expected) || NND_RegistryRecordGuards.bad1 m s reg
 then ok (.Err .InvalidAccountData)
 else NND_Entry1Readonly.run (NND_RegistryOps.install base D env) v m.key rp e t := by
 simp only [NND_Registry1Guard.run,NND_RegistryStd.key_ne,NND_RegistryScalarOps.to_bytes,
  NND_RegistryFlagValues.paused1,NND_RegistryFlagValues.immutable1,
  NGL_ArrayEquality.ne_value,r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,
  NND_RegistryRecordGuards.bad1,NND_BoolReject.not_guard]
 exact NND_BoolReject.six _ _ _ _ _ _ _ _

#print axioms value
end NND_Registry1GuardValue
end
