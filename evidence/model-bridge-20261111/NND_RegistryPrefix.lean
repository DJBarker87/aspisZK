import NND_RegistryFactor
import NND_RegistryArgs
import NND_RegistryReplies
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NND_RegistryPrefix
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (next : Array U8 32#usize → Result (core.result.Result Unit solana_program_error.ProgramError)) :
 NND_RegistryFactor.head (NND_RegistryOps.install base D env) v p m s r e t next =
 if NND_RegistryArgs.policyBad D p s then ok (.Err .InvalidAccountData) else
 match NND_RegistryReplies.policy s.verifier_policy with
 | .Err _ => ok (.Err .InvalidAccountData)
 | .Ok _ => next (NND_Carrier.unkey D.registry) := by
 unfold NND_RegistryFactor.head NND_RegistryArgs.policyBad
 simp only [NND_RegistryOps.install,NGL_ArrayEquality.ne_value,lift,bind_tc_ok,
   NND_RegistryReplies.policy_eq]
 by_cases h0 : p = NND_Carrier.unkey D.pool
 · simp only [h0,decide_true,Bool.not_true,Bool.false_eq_true,if_false,Bool.false_or]
   by_cases h1 : s.verifier_policy.flags &&& 1#u8 = 0#u8
   · simp [h1]
   · simp only [h1,if_false,decide_false,Bool.false_or]
     by_cases h2 : s.verifier_policy.registry_program = NND_Carrier.unkey D.registry
     · simp only [h2,decide_true,Bool.not_true,Bool.false_eq_true,if_false,Bool.false_or]
       by_cases h3 : s.verifier_policy.registry_authority = Array.repeat 32#usize 0#u8
       · simp only [h3,decide_true,Bool.not_true,Bool.false_eq_true,if_false,Bool.false_or]
         by_cases h4 : s.verifier_policy.policy_binding = r1_pool_adapter.AUDIT_POLICY_BINDING
         · simp only [h4,decide_true,Bool.not_true,Bool.false_eq_true,if_false,Bool.false_or]
           cases hp : NND_RegistryReplies.policy s.verifier_policy with
           | Err err => rfl
           | Ok u => cases u; rfl
         · simp [h4]
       · simp [h3]
     · simp [h2]
 · simp [h0]

#print axioms value
end NND_RegistryPrefix
end
