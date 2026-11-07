import NNH_MRegistry1Guard
import NND_BoolReject
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry1GuardValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v rp : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1)
 (expected : solana_pubkey.Pubkey) :
 NNH_MRegistry1Guard.run (NNH_MRegistryOps.install base D env) v m.key rp s r e t reg expected =
 if !decide (r.key = expected) || NNH_MRegistryRecordGuards.bad1 m s reg
 then ok (.Err .InvalidAccountData)
 else NNH_MEntry1Readonly.run (NNH_MRegistryOps.install base D env) v m.key rp e t := by
 simp only [NNH_MRegistry1Guard.run,NNH_MRegistryStd.key_ne,NNH_MRegistryScalarOps.to_bytes,
  NNH_MRegistryFlagValues.paused1,NNH_MRegistryFlagValues.immutable1,
  NGL_ArrayEquality.ne_value,r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,
  NNH_MRegistryRecordGuards.bad1,NND_BoolReject.not_guard]
 exact NND_BoolReject.six _ _ _ _ _ _ _ _

#print axioms value
end NNH_MRegistry1GuardValue
end
