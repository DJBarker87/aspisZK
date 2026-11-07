import NNH_MRegistryPrefix
import NND_PoolReturned
import NND_ReplyForth
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryPolicyFold
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rest : Except RSL.ProgramError Unit) :
 outer (reply id)
  (NND_RegistryFactor.head (NNH_MRegistryOps.install base D env) v p m s r e t
   (fun _ => ok (unreply id rest))) =
 ok (eseq (echeck (RSL.TX2_234.policyBad D (NNH_MRegistryArgs.args v p m s r e t)) .invalidAccountData)
  (eseq (echeck (!(NNH_MRegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy)) .invalidAccountData) rest)) := by
 rw [NNH_MRegistryPrefix.value base L D env v p m s r e t]
 rw [NNH_MRegistryArgs.policy_bad]
 have policy : (NNH_MRegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy) =
 NNH_MPolicyValue.isOk (NNH_MRegistryReplies.policy s.verifier_policy) := by
  unfold NNH_MRegistryLibrary.install NNH_MPolicyValue.validate
  simp only [NNH_MPolicyValue.back]
  rfl
 rw [policy]
 cases bad : RSL.TX2_234.policyBad D (NNH_MRegistryArgs.args v p m s r e t)
 · simp only [bad,Bool.false_eq_true,if_false,echeck,eseq,ebind]
   cases checked : NNH_MRegistryReplies.policy s.verifier_policy with
   | Err err => rfl
   | Ok u =>
     cases u
     change ok (reply id (unreply id rest)) = ok rest
     rw [reply_forth id id (fun _ => rfl)]
 · rfl

#print axioms value
end NNH_MRegistryPolicyFold
end
