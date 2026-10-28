import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
import PV_L1_Source_070
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_071
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  {T0 : Type}
  (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst :
  core.ops.function.FnMut T0 Std.Usize (core.result.Result
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error))
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (next_attempt : T0) (k : Std.Usize) :
  Logged ((core.result.Result prover.RetriedProof verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  := do
  let _ ← observe .opening 0 (ok ())
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
        PV_L1_Source_070.produce public1 compiled variant hash val
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
          prover.retry_attempt
            coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst
            public1 compiled variant hash nonce_store1 next_attempt1 i
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

theorem complete_result
  {T0 : Type}
  (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst :
  core.ops.function.FnMut T0 Std.Usize (core.result.Result
  aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error))
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
  (variant : transport.Variant)
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize))
  (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
  (next_attempt : T0) (k : Std.Usize) :
  erase (produce (T0 := T0) coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k) = prover.retry_attempt (T0 := T0) coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k := by
  unfold produce prover.retry_attempt
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_070.complete_result]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1_Source_070.complete_result]
#print axioms complete_result
end PV_L1_Source_071
