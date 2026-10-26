import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PDict_RetryCap
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- No entropy or proof-body premise is needed at the exhausted source cap. -/
theorem cap {C : Type}
    (entropy : core.ops.function.FnMut C Usize (core.result.Result
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error))
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (callback : C) (k : Usize) (hk : 8 ≤ k.val) :
    prover.retry_attempt entropy pub compiled v hash store callback k =
      .ok (.Err verifier.Error.AttemptsExhausted,store) := by
  have guard : k >= prover.ATTEMPT_CAP := by
    simp only [prover.ATTEMPT_CAP]
    change 8 ≤ k.val
    exact hk
  rw [prover.retry_attempt]
  simp only [guard,if_true]

#print axioms cap
end R1Z.PDict_RetryCap
