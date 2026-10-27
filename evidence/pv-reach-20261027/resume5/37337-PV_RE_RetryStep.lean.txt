import R1Z.PV_RE_CapValue
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_RetryStep
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Compiled := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Entropy (C : Type) := core.ops.function.FnMut C Usize (core.result.Result Secrets verifier.Error)
abbrev Reply := Result ((core.result.Result prover.RetriedProof verifier.Error) × Store)

def step
  {T0 : Type}
  (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst :
  core.ops.function.FnMut T0 Std.Usize (core.result.Result
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error))
  (next : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore → T0 → Std.Usize →
    Result ((core.result.Result prover.RetriedProof verifier.Error) ×
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore))
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (next_attempt : T0) (k : Std.Usize) :
  Result ((core.result.Result prover.RetriedProof verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  if k >= prover.ATTEMPT_CAP
  then
    ok (core.result.Result.Err verifier.Error.AttemptsExhausted, nonce_store)
  else
    let (r, next_attempt1) ←
      coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut
        next_attempt k
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, nonce_store1) ←
        prover.prove_masked_attempt public1 compiled variant hash val
          nonce_store
      match r1 with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
        ok (core.result.Result.Ok { proof, audit, attempts := i },
          nonce_store1)
      | core.result.Result.Err e =>
        match e with
        | verifier.Error.Parse =>
          ok (core.result.Result.Err verifier.Error.Parse, nonce_store1)
        | verifier.Error.Semantic =>
          ok (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
        | verifier.Error.Transcript =>
          ok (core.result.Result.Err verifier.Error.Transcript, nonce_store1)
        | verifier.Error.Relation =>
          ok (core.result.Result.Err verifier.Error.Relation, nonce_store1)
        | verifier.Error.Merkle =>
          ok (core.result.Result.Err verifier.Error.Merkle, nonce_store1)
        | verifier.Error.Query =>
          ok (core.result.Result.Err verifier.Error.Query, nonce_store1)
        | verifier.Error.Checkpoint =>
          ok (core.result.Result.Err verifier.Error.Checkpoint, nonce_store1)
        | verifier.Error.Allocation =>
          ok (core.result.Result.Err verifier.Error.Allocation, nonce_store1)
        | verifier.Error.Rejected =>
          let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
          next nonce_store1 next_attempt1 i
        | verifier.Error.AttemptsExhausted =>
          ok (core.result.Result.Err verifier.Error.AttemptsExhausted,
            nonce_store1)
        | verifier.Error.Entropy =>
          ok (core.result.Result.Err verifier.Error.Entropy, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.RetriedProof (core.convert.FromSame verifier.Error) residual
      ok (r1, nonce_store)

/-- Complete one-step retry equation, including every continuation and error. -/
theorem unfold_retry {C : Type} (entropy : Entropy C) (pub : Public)
    (compiled : Compiled) (v : transport.Variant) (hash : Hash)
    (store : Store) (state : C) (k : Usize) :
    prover.retry_attempt entropy pub compiled v hash store state k =
      step entropy (prover.retry_attempt entropy pub compiled v hash) pub compiled v hash store state k := by
  rw [prover.retry_attempt]
  rfl

#print axioms step
#print axioms unfold_retry
end R1Z.PV_RE_RetryStep
