import NND_RegistryRouteValue
import NND_RegistryPolicyFold
set_option autoImplicit false
noncomputable section
namespace NND_RegistryFullValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) :
 outer (reply id)
 (r1_pool_adapter.owned.authenticate_invariant_release_registry (NND_RegistryOps.install base D env) v p m s r e t) =
 ok (NND_RegistryEval.value (NND_RegistryLibrary.install L) D (NND_RegistryArgs.args v p m s r e t) env) := by
 rw [←NND_Registry.adopted,NND_RegistryFactor.source,NND_RegistryPrefix.value base L D env v p m s r e t]
 rw [NND_RegistryArgs.policy_bad]
 have policy : (NND_RegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy) =
 NND_PolicyValue.isOk (NND_RegistryReplies.policy s.verifier_policy) := by
  unfold NND_RegistryLibrary.install NND_PolicyValue.validate
  simp only [NND_PolicyValue.back]
  rfl
 unfold NND_RegistryEval.value
 change _ = ok (eseq (echeck (RSL.TX2_234.policyBad D (NND_RegistryArgs.args v p m s r e t)) .invalidAccountData)
  (eseq (echeck (!(NND_RegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy)) .invalidAccountData)
   (NND_RegistryRouteValue.tail L D (NND_RegistryArgs.args v p m s r e t) env)))
 rw [policy]
 cases bad : RSL.TX2_234.policyBad D (NND_RegistryArgs.args v p m s r e t)
 · simp only [bad,Bool.false_eq_true,if_false,echeck,eseq,ebind]
   cases checked : NND_RegistryReplies.policy s.verifier_policy with
   | Err err => rfl
   | Ok u =>
     cases u
     exact NND_RegistryRouteValue.value base L D env v p m s r e t
 · rfl

#print axioms value
end NND_RegistryFullValue
end
