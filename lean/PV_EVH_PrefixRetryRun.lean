import PV_EVH_RetrySource
import PV_EVH_PrefixRetryBody
import PV_EVH_PrefixLoop
set_option autoImplicit false
noncomputable section
namespace PV_EVH_PrefixRetryRun
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World PV_EVH_WorldLoop
open PV_EVH_RetryBody (State Outcome sourceBody)
open PV_EVH_PrefixRetryBody
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
/-- Finite source retry execution with two uninstantiated callee interpretations.
Nested finite exhaustion is preserved. This is not a complete proof-account worldRun. -/
def run (fuel : Nat)
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
  (next_attempt : T0) (k : Std.Usize) (next_OPEN : NextP T0) (prove_OPEN : ProveP) : World → Prefix Outcome :=
  PV_EVH_PrefixLoop.loop (fun s => body coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash s.1 s.2.1 s.2.2 next_OPEN prove_OPEN)
    fuel (nonce_store,next_attempt,k)

theorem run_fixed (fuel : Nat)
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
      (prover.prove_masked_attempt public1 compiled variant hash a st))
    (w : World) (r : Result Outcome)
    (finished : (run fuel coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k next_OPEN prove_OPEN w).status = .finished r) :
    prover.retry_attempt coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k = r := by
  exact PV_EVH_PrefixLoop.fixed_recursive (S := State T0) (A := Outcome)
    (fun s => body coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash s.1 s.2.1 s.2.2 next_OPEN prove_OPEN)
    (fun s => sourceBody coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash s.1 s.2.1 s.2.2)
    (fun s => prover.retry_attempt coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash s.1 s.2.1 s.2.2)
    (by
      rintro ⟨st,c,i⟩
      rw [PV_EVH_RetrySource.source_unfold coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i]
      congr 1
      funext cf
      cases cf with
      | done a => rfl
      | cont next => rcases next with ⟨st,c,i⟩; rfl)
    (fun s => body_fixed coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash s.1 s.2.1 s.2.2 next_OPEN prove_OPEN next_fixed prove_fixed)
    fuel (nonce_store,next_attempt,k) w r finished

#print axioms run_fixed
end PV_EVH_PrefixRetryRun
