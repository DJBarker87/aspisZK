import PV_EVH_WorldLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RetryBody
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Outcome := (core.result.Result prover.RetriedProof verifier.Error) × Store
abbrev AttemptOutcome := (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error) × Store
abbrev Next (T : Type) := T → Usize → M ((core.result.Result Secrets verifier.Error) × T)
abbrev Prove := Secrets → Store → M AttemptOutcome
abbrev State (T : Type) := Store × T × Usize

def sourceBody
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
  (next_attempt : T0) (k : Std.Usize) : Result (ControlFlow (State T0) Outcome) := do
  if k >= prover.ATTEMPT_CAP then
    Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.AttemptsExhausted, nonce_store)))
  else
    let (r, next_attempt1) ← coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut
        next_attempt k
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, nonce_store1) ← prover.prove_masked_attempt public1 compiled variant hash val
          nonce_store
      match r1 with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
        Result.ok (ControlFlow.done ((core.result.Result.Ok { proof, audit, attempts := i },
nonce_store1)))
      | core.result.Result.Err e =>
        match e with
        | verifier.Error.Parse =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Parse, nonce_store1)))
        | verifier.Error.Semantic =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Semantic, nonce_store1)))
        | verifier.Error.Transcript =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Transcript, nonce_store1)))
        | verifier.Error.Relation =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Relation, nonce_store1)))
        | verifier.Error.Merkle =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Merkle, nonce_store1)))
        | verifier.Error.Query =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Query, nonce_store1)))
        | verifier.Error.Checkpoint =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Checkpoint, nonce_store1)))
        | verifier.Error.Allocation =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Allocation, nonce_store1)))
        | verifier.Error.Rejected =>
          let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
          Result.ok (ControlFlow.cont (nonce_store1, next_attempt1, i))
        | verifier.Error.AttemptsExhausted =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.AttemptsExhausted,
nonce_store1)))
        | verifier.Error.Entropy =>
          Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Entropy, nonce_store1)))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          prover.RetriedProof (core.convert.FromSame verifier.Error) residual
      Result.ok (ControlFlow.done ((r1, nonce_store)))

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
  (next_attempt : T0) (k : Std.Usize) (next_OPEN : Next T0) (prove_OPEN : Prove) : M (ControlFlow (State T0) Outcome) := do
  if k >= prover.ATTEMPT_CAP then
    pure (ControlFlow.done ((core.result.Result.Err verifier.Error.AttemptsExhausted, nonce_store)))
  else
    let (r, next_attempt1) ← next_OPEN next_attempt k
    let cf ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTry.branch r)
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r1, nonce_store1) ← (do
          let _ ← PV_EVH_World.attempt
          prove_OPEN val nonce_store)
      match r1 with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← PV_EVH_World.lift (Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))
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
          let i ← PV_EVH_World.lift (Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))
          do
            let _ ← PV_EVH_World.retry
            pure (ControlFlow.cont (nonce_store1, next_attempt1, i))
        | verifier.Error.AttemptsExhausted =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.AttemptsExhausted,
nonce_store1)))
        | verifier.Error.Entropy =>
          pure (ControlFlow.done ((core.result.Result.Err verifier.Error.Entropy, nonce_store1)))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ← PV_EVH_World.lift (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
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
  (next_attempt : T0) (k : Std.Usize) (next_OPEN : Next T0) (prove_OPEN : Prove)
    (next_fixed : ∀ c k, FixedView (next_OPEN c k)
      (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut c k))
    (prove_fixed : ∀ a st, FixedView (prove_OPEN a st)
      (prover.prove_masked_attempt public1 compiled variant hash a st)) :
    FixedView (body coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k next_OPEN prove_OPEN)
      (sourceBody coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k) := by
  unfold body sourceBody
  by_cases condition : k >= prover.ATTEMPT_CAP
  · simp only [condition,if_true]
    exact fixed_lift _
  · simp only [condition,if_false]
    try dsimp only
    apply fixed_bind
    ·
      exact next_fixed _ _
    · rintro ⟨r, next_attempt1⟩
      try dsimp only
      apply fixed_bind
      ·
        exact fixed_lift _
      · intro cf
        try dsimp only
        cases cf with
        | Continue val =>
          try dsimp only
          apply fixed_bind
          ·
            intro w
            exact prove_fixed _ _ _
          · rintro ⟨r1, nonce_store1⟩
            try dsimp only
            cases r1 with
            | Ok p =>
              let (proof, audit) := p
              try dsimp only
              try dsimp only
              apply fixed_bind (r := (do
                Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))) (f := fun i => (show Result (ControlFlow (State T0) Outcome) from do
                Result.ok (ControlFlow.done ((core.result.Result.Ok { proof, audit, attempts := i },
nonce_store1)))))
              ·
                exact fixed_lift _
              · intro i
                exact fixed_lift _
            | Err e =>
              try dsimp only
              cases e with
              | Parse =>
                exact fixed_lift _
              | Semantic =>
                exact fixed_lift _
              | Transcript =>
                exact fixed_lift _
              | Relation =>
                exact fixed_lift _
              | Merkle =>
                exact fixed_lift _
              | Query =>
                exact fixed_lift _
              | Checkpoint =>
                exact fixed_lift _
              | Allocation =>
                exact fixed_lift _
              | Rejected =>
                try dsimp only
                apply fixed_bind (r := (do
                  Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize))) (f := fun i => (show Result (ControlFlow (State T0) Outcome) from do
                  Result.ok (ControlFlow.cont (nonce_store1, next_attempt1, i))))
                ·
                  exact fixed_lift _
                · intro i
                  intro w; rfl
              | AttemptsExhausted =>
                exact fixed_lift _
              | Entropy =>
                exact fixed_lift _
        | Break residual =>
          try dsimp only
          apply fixed_bind
          ·
            exact fixed_lift _
          · intro r1
            exact fixed_lift _

#print axioms body_fixed
end PV_EVH_RetryBody
