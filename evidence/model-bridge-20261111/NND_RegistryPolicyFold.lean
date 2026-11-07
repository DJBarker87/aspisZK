import NND_RegistryPrefix
import NND_PoolReturned
import NND_ReplyForth
set_option autoImplicit false
noncomputable section
namespace NND_RegistryPolicyFold
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rest : Except RSL.ProgramError Unit) :
 outer (reply id)
  (NND_RegistryFactor.head (NND_RegistryOps.install base D env) v p m s r e t
   (fun _ => ok (unreply id rest))) =
 ok (eseq (echeck (RSL.TX2_234.policyBad D (NND_RegistryArgs.args v p m s r e t)) .invalidAccountData)
  (eseq (echeck (!(NND_RegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy)) .invalidAccountData) rest)) := by
 rw [NND_RegistryPrefix.value base L D env v p m s r e t]
 rw [NND_RegistryArgs.policy_bad]
 have policy : (NND_RegistryLibrary.install L).validatePolicy (NND_Carrier.policy s.verifier_policy) =
 NND_PolicyValue.isOk (NND_RegistryReplies.policy s.verifier_policy) := by
  unfold NND_RegistryLibrary.install NND_PolicyValue.validate
  simp only [NND_PolicyValue.back]
  rfl
 rw [policy]
 cases bad : RSL.TX2_234.policyBad D (NND_RegistryArgs.args v p m s r e t)
 · simp only [bad,Bool.false_eq_true,if_false,echeck,eseq,ebind]
   cases checked : NND_RegistryReplies.policy s.verifier_policy with
   | Err err => rfl
   | Ok u =>
     cases u
     change ok (reply id (unreply id rest)) = ok rest
     rw [reply_forth id id (fun _ => rfl)]
 · rfl

#print axioms value
end NND_RegistryPolicyFold
end
