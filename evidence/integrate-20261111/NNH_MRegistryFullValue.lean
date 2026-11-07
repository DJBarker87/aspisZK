import NNH_MRegistryRouteValue
import NNH_MRegistryPolicyFold
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryFullValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id)
 (r1_pool_adapter.owned.authenticate_invariant_release_registry (NNH_MRegistryOps.install base D env) v p m s r e t) =
 ok (NNH_RegistryEval.value (NNH_MRegistryLibrary.install L) D (NNH_MRegistryArgs.args v p m s r e t) env) := by
 rw [←NND_Registry.adopted,NND_RegistryFactor.source,NNH_MRegistryPrefix.value base L D env v p m s r e t]
 rw [NNH_MRegistryArgs.policy_bad]
 have policy : (NNH_MRegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy) =
 NNH_MPolicyValue.isOk (NNH_MRegistryReplies.policy s.verifier_policy) := by
  unfold NNH_MRegistryLibrary.install NNH_MPolicyValue.validate
  simp only [NNH_MPolicyValue.back]
  rfl
 unfold NNH_RegistryEval.value
 change _ = ok (eseq (echeck (RSL.TX2_234.policyBad D (NNH_MRegistryArgs.args v p m s r e t)) .invalidAccountData)
  (eseq (echeck (!(NNH_MRegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy)) .invalidAccountData)
   (NNH_MRegistryRouteValue.tail L D (NNH_MRegistryArgs.args v p m s r e t) env)))
 rw [policy]
 cases bad : RSL.TX2_234.policyBad D (NNH_MRegistryArgs.args v p m s r e t)
 · simp only [bad,Bool.false_eq_true,if_false,echeck,eseq,ebind]
   cases checked : NNH_MRegistryReplies.policy s.verifier_policy with
   | Err err => rfl
   | Ok u =>
     cases u
     exact NNH_MRegistryRouteValue.value base L D env v p m s r e t
 · rfl

#print axioms value
end NNH_MRegistryFullValue
end
