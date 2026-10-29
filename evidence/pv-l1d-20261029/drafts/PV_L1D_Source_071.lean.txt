import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
import PV_L1D_Source_070
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_071
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
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
    Pure.pure (core.result.Result.Err verifier.Error.AttemptsExhausted, nonce_store)
  else
    let (r, next_attempt1) ← PV_L1D_Logged.lift (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut
        next_attempt k)
    let cf ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, nonce_store1) ←
        PV_L1D_Source_070.produce public1 compiled variant hash val
          nonce_store
      match r1 with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))
        Pure.pure (core.result.Result.Ok { proof, audit, attempts := i },
          nonce_store1)
      | core.result.Result.Err e =>
        match e with
        | verifier.Error.Parse =>
          Pure.pure (core.result.Result.Err verifier.Error.Parse, nonce_store1)
        | verifier.Error.Semantic =>
          Pure.pure (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
        | verifier.Error.Transcript =>
          Pure.pure (core.result.Result.Err verifier.Error.Transcript, nonce_store1)
        | verifier.Error.Relation =>
          Pure.pure (core.result.Result.Err verifier.Error.Relation, nonce_store1)
        | verifier.Error.Merkle =>
          Pure.pure (core.result.Result.Err verifier.Error.Merkle, nonce_store1)
        | verifier.Error.Query =>
          Pure.pure (core.result.Result.Err verifier.Error.Query, nonce_store1)
        | verifier.Error.Checkpoint =>
          Pure.pure (core.result.Result.Err verifier.Error.Checkpoint, nonce_store1)
        | verifier.Error.Allocation =>
          Pure.pure (core.result.Result.Err verifier.Error.Allocation, nonce_store1)
        | verifier.Error.Rejected =>
          let i ← PV_L1D_Logged.lift (Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))
          prover.retry_attempt
            coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst
            public1 compiled variant hash nonce_store1 next_attempt1 i
        | verifier.Error.AttemptsExhausted =>
          Pure.pure (core.result.Result.Err verifier.Error.AttemptsExhausted,
            nonce_store1)
        | verifier.Error.Entropy =>
          Pure.pure (core.result.Result.Err verifier.Error.Entropy, nonce_store1)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← PV_L1D_Logged.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.RetriedProof (core.convert.FromSame verifier.Error) residual)
      Pure.pure (r1, nonce_store)

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
  unfold produce
  conv_rhs => unfold prover.retry_attempt
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_070.complete_result]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_070.complete_result]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure,PV_L1D_Source_070.complete_result]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_071
