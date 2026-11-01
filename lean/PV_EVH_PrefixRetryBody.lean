import PV_EVH_Prefix
import PV_EVH_RetryBody
set_option autoImplicit false
noncomputable section
namespace PV_EVH_PrefixRetryBody
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_RetryBody (Store Secrets Outcome AttemptOutcome State sourceBody)
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
abbrev NextP (T : Type) := T → Usize → P ((core.result.Result Secrets verifier.Error) × T)
abbrev ProveP := Secrets → Store → P AttemptOutcome

/-- Only the retry source spine. Both callee interpreters are OPEN. -/
def body
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
  (next_attempt : T0) (k : Std.Usize) (next_OPEN : NextP T0) (prove_OPEN : ProveP) : P (ControlFlow (State T0) Outcome) := do
  if k >= prover.ATTEMPT_CAP then
    pure (ControlFlow.done ((core.result.Result.Err verifier.Error.AttemptsExhausted, nonce_store)))
  else
    let (r, next_attempt1) ← next_OPEN next_attempt k
    let cf ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, nonce_store1) ← (do
          let _ ← PV_EVH_Prefix.ofM PV_EVH_World.attempt
          prove_OPEN val nonce_store)
      match r1 with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))
        pure (ControlFlow.done ((core.result.Result.Ok { proof, audit, attempts := i },
nonce_store1)))
      | core.result.Result.Err e =>
        match e with
        | verifier.Error.Parse =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Parse, nonce_store1)))
        | verifier.Error.Semantic =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Semantic, nonce_store1)))
        | verifier.Error.Transcript =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Transcript, nonce_store1)))
        | verifier.Error.Relation =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Relation, nonce_store1)))
        | verifier.Error.Merkle =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Merkle, nonce_store1)))
        | verifier.Error.Query =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Query, nonce_store1)))
        | verifier.Error.Checkpoint =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Checkpoint, nonce_store1)))
        | verifier.Error.Allocation =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Allocation, nonce_store1)))
        | verifier.Error.Rejected =>
          let i ← PV_EVH_Prefix.lift (Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))
          do
            let _ ← PV_EVH_Prefix.ofM PV_EVH_World.retry
            pure (ControlFlow.cont (nonce_store1, next_attempt1, i))
        | verifier.Error.AttemptsExhausted =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.AttemptsExhausted,
nonce_store1)))
        | verifier.Error.Entropy =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Entropy, nonce_store1)))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← PV_EVH_Prefix.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.RetriedProof (core.convert.FromSame verifier.Error) residual)
      pure (ControlFlow.done ((r1, nonce_store)))

theorem body_fixed
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
  (next_attempt : T0) (k : Std.Usize) (next_OPEN : NextP T0) (prove_OPEN : ProveP)
    (next_fixed : ∀ c k, FinishedView (next_OPEN c k)
      (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut c k))
    (prove_fixed : ∀ a st, FinishedView (prove_OPEN a st)
      (prover.prove_masked_attempt public1 compiled variant hash a st)) :
    FinishedView (body coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k next_OPEN prove_OPEN)
      (sourceBody coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k) := by
  unfold body sourceBody
  by_cases condition : k >= prover.ATTEMPT_CAP
  · simp only [condition,if_true]
    exact PV_EVH_Prefix.lift_fixed _
  · simp only [condition,if_false]
    try dsimp only
    apply PV_EVH_Prefix.bind_fixed
    ·
      exact next_fixed _ _
    · rintro ⟨r, next_attempt1⟩
      try dsimp only
      apply PV_EVH_Prefix.bind_fixed
      ·
        exact PV_EVH_Prefix.lift_fixed _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            apply PV_EVH_Prefix.bind_fixed (r := .ok ())
              (f := fun _ => prover.prove_masked_attempt public1 compiled variant hash val nonce_store)
            · exact PV_EVH_Prefix.ofM_fixed _ _ (fun _ => rfl)
            · intro unused
              exact prove_fixed _ _
          · rintro ⟨r1, nonce_store1⟩
            try dsimp only
            cases r1 with
            | Ok p =>
              let (proof, audit) := p
              try dsimp only
              try dsimp only
              apply PV_EVH_Prefix.bind_fixed (r := (do
                Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))) (f := fun i => (show Result (ControlFlow (State T0) Outcome) from do
                Result.ok (ControlFlow.done ((core.result.Result.Ok { proof, audit, attempts := i },
nonce_store1)))))
              ·
                exact PV_EVH_Prefix.lift_fixed _
              · intro i
                exact PV_EVH_Prefix.lift_fixed _
            | Err e =>
              try dsimp only
              cases e with
              | Parse =>
                exact PV_EVH_Prefix.lift_fixed _
              | Semantic =>
                exact PV_EVH_Prefix.lift_fixed _
              | Transcript =>
                exact PV_EVH_Prefix.lift_fixed _
              | Relation =>
                exact PV_EVH_Prefix.lift_fixed _
              | Merkle =>
                exact PV_EVH_Prefix.lift_fixed _
              | Query =>
                exact PV_EVH_Prefix.lift_fixed _
              | Checkpoint =>
                exact PV_EVH_Prefix.lift_fixed _
              | Allocation =>
                exact PV_EVH_Prefix.lift_fixed _
              | Rejected =>
                try dsimp only
                apply PV_EVH_Prefix.bind_fixed (r := (do
                  Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))) (f := fun i => (show Result (ControlFlow (State T0) Outcome) from do
                  Result.ok (ControlFlow.cont (nonce_store1, next_attempt1, i))))
                ·
                  exact PV_EVH_Prefix.lift_fixed _
                · intro i
                  intro w r h; cases h; rfl
              | AttemptsExhausted =>
                exact PV_EVH_Prefix.lift_fixed _
              | Entropy =>
                exact PV_EVH_Prefix.lift_fixed _
        | Break residual =>
          try dsimp only
          apply PV_EVH_Prefix.bind_fixed
          ·
            exact PV_EVH_Prefix.lift_fixed _
          · intro r1
            exact PV_EVH_Prefix.lift_fixed _


#print axioms body_fixed
end PV_EVH_PrefixRetryBody
