import PV_EVH_RetryBody
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RetrySource
open Aeneas Aeneas.Std ProverRwFull PV_EVH_RetryBody
variable [ExternalTypes] [ExternalFuns]

private theorem prod_case {A B C : Type} (p : A × B) (f : A → B → C) :
    (match p with | (a,b) => f a b) = f p.1 p.2 := by
  cases p; rfl

theorem source_unfold
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
    prover.retry_attempt coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k =
    Aeneas.Std.bind (sourceBody coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k) (fun cf =>
      match cf with
      | .done a => .ok a
      | .cont (st,c,i) => prover.retry_attempt coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i) := by
  rw [prover.retry_attempt.eq_def]
  unfold sourceBody
  by_cases condition : k ≥ prover.ATTEMPT_CAP
  · simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [condition,if_true,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div, prod_case]
  · simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [condition,if_false]
    cases hn : coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut next_attempt k with
    | fail e => simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [hn,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div, prod_case]
    | div => simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [hn,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div, prod_case]
    | ok pair =>
      rcases pair with ⟨r,c⟩
      simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [hn,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div, prod_case]
      cases r with
      | Err e => rfl
      | Ok val =>
          change (show Result Outcome from do
            let (r1, nonce_store1) ← prover.prove_masked_attempt public1 compiled variant hash val
                nonce_store
            match r1 with
            | core.result.Result.Ok p =>
              let (proof, audit) := p
              let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
              Result.ok (core.result.Result.Ok { proof, audit, attempts := i },
nonce_store1)
            | core.result.Result.Err e =>
              match e with
              | verifier.Error.Parse =>
                Result.ok (core.result.Result.Err verifier.Error.Parse, nonce_store1)
              | verifier.Error.Semantic =>
                Result.ok (core.result.Result.Err verifier.Error.Semantic, nonce_store1)
              | verifier.Error.Transcript =>
                Result.ok (core.result.Result.Err verifier.Error.Transcript, nonce_store1)
              | verifier.Error.Relation =>
                Result.ok (core.result.Result.Err verifier.Error.Relation, nonce_store1)
              | verifier.Error.Merkle =>
                Result.ok (core.result.Result.Err verifier.Error.Merkle, nonce_store1)
              | verifier.Error.Query =>
                Result.ok (core.result.Result.Err verifier.Error.Query, nonce_store1)
              | verifier.Error.Checkpoint =>
                Result.ok (core.result.Result.Err verifier.Error.Checkpoint, nonce_store1)
              | verifier.Error.Allocation =>
                Result.ok (core.result.Result.Err verifier.Error.Allocation, nonce_store1)
              | verifier.Error.Rejected =>
                let i ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
                prover.retry_attempt
                  coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst
                  public1 compiled variant hash nonce_store1 c i
              | verifier.Error.AttemptsExhausted =>
                Result.ok (core.result.Result.Err verifier.Error.AttemptsExhausted,
nonce_store1)
              | verifier.Error.Entropy =>
                Result.ok (core.result.Result.Err verifier.Error.Entropy, nonce_store1)) =
            Aeneas.Std.bind (show Result (ControlFlow (State T0) Outcome) from do
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
                  Result.ok (ControlFlow.cont (nonce_store1, c, i))
                | verifier.Error.AttemptsExhausted =>
                  Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.AttemptsExhausted,
nonce_store1)))
                | verifier.Error.Entropy =>
                  Result.ok (ControlFlow.done ((core.result.Result.Err verifier.Error.Entropy, nonce_store1)))) (fun cf => match cf with | .done a => .ok a | .cont (st,c,i) => prover.retry_attempt coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i)
          cases hp : prover.prove_masked_attempt public1 compiled variant hash val nonce_store with
          | fail e => rfl
          | div => rfl
          | ok pair =>
            rcases pair with ⟨p,st⟩
            simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [prod_case, Aeneas.Std.bind_tc_ok]
            cases p with
            | Ok pair =>
              rcases pair with ⟨proof,audit⟩
              cases hi : Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize) <;>
                simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [hi,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div, prod_case]
            | Err e =>
              cases e <;> try rfl
              cases hi : Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize) <;>
                simp (config := { zeta := true, zetaDelta := true, zetaHave := true }) only [hi,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div, prod_case]

#print axioms source_unfold
end PV_EVH_RetrySource
