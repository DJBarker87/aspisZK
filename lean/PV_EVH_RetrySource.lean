import PV_EVH_RetryBody
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RetrySource
open Aeneas Aeneas.Std ProverRwFull PV_EVH_RetryBody
variable [ExternalTypes] [ExternalFuns]

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
  · simp only [condition,if_true,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
  · simp only [condition,if_false]
    cases hn : coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut next_attempt k with
    | fail e => simp only [hn,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
    | div => simp only [hn,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
    | ok pair =>
      rcases pair with ⟨r,c⟩
      simp only [hn,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
      cases r with
      | Err e => rfl
      | Ok val =>
          dsimp only [core.result.Result.Insts.CoreOpsTry.branch]
          simp only [Aeneas.Std.bind_tc_ok]
          cases hp : prover.prove_masked_attempt public1 compiled variant hash val nonce_store with
          | fail e => simp only [hp,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
          | div => simp only [hp,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
          | ok pair =>
            rcases pair with ⟨p,st⟩
            simp only [hp,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
            cases p with
            | Ok pair =>
              rcases pair with ⟨proof,audit⟩
              cases hi : Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize) <;>
                simp only [hi,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]
            | Err e =>
              cases e <;> try rfl
              cases hi : Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize) <;>
                simp only [hi,Aeneas.Std.bind, Aeneas.Std.bind_tc_ok, Aeneas.Std.bind_tc_fail, Aeneas.Std.bind_tc_div]

#print axioms source_unfold
end PV_EVH_RetrySource
