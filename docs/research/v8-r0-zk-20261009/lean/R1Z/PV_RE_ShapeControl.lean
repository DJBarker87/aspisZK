import R1Z.PV_RE_ContinuationRetry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ShapeControl
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep
variable [ExternalTypes] [ExternalFuns]

/-- Exact complete outer control on the transfer constructor. This does not
assert a native fixture association or a dictionary-invocation trace. -/
theorem transfer {C : Type}
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    RealR1_client.prove_for_proof_accounts entropy (.Transfer p transition) compiled hash store state =
      (ExternalFuns.op233 .S2 .S2 >>= fun equal =>
        if !equal then .ok (.Err .Semantic,store)
        else PV_RE_ContinuationRetry.runCPS
          (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
          (.Transfer p transition) compiled .S2 hash 8 store state 0#usize) := by
  exact PV_RE_ContinuationRetry.whole_client entropy (.Transfer p transition) compiled hash store state

#print axioms transfer

/-- Exact complete outer control on the withdrawal constructor. This does not
assert a native fixture association or a dictionary-invocation trace. -/
theorem withdrawal {C : Type}
    (entropy : core.ops.function.FnMut C Usize (Array U8 32#usize))
    (p : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (compiled : Compiled) (hash : Hash) (store : Store) (state : C) :
    RealR1_client.prove_for_proof_accounts entropy (.Withdrawal p transition) compiled hash store state =
      (ExternalFuns.op233 .S2 .S2 >>= fun equal =>
        if !equal then .ok (.Err .Semantic,store)
        else PV_RE_ContinuationRetry.runCPS
          (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError entropy)
          (.Withdrawal p transition) compiled .S2 hash 8 store state 0#usize) := by
  exact PV_RE_ContinuationRetry.whole_client entropy (.Withdrawal p transition) compiled hash store state

#print axioms withdrawal
end R1Z.PV_RE_ShapeControl
