import PV_EVH_RetrySource
import PV_EVH_WorldRecursion
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RetryRun
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_World PV_EVH_WorldLoop PV_EVH_RetryBody
variable [ExternalTypes] [ExternalFuns]
/-- Finite source retry execution with two uninstantiated callee interpretations.
This is not a complete proof-account worldRun. -/
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
  (next_attempt : T0) (k : Std.Usize) (next_OPEN : Next T0) (prove_OPEN : Prove) : World → Prefix Outcome :=
  PV_EVH_WorldLoop.loop (fun (st,c,i) => body coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i next_OPEN prove_OPEN)
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
  (next_attempt : T0) (k : Std.Usize) (next_OPEN : Next T0) (prove_OPEN : Prove)
    (next_fixed : ∀ c k, FixedView (next_OPEN c k)
      (coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst.call_mut c k))
    (prove_fixed : ∀ a st, FixedView (prove_OPEN a st)
      (prover.prove_masked_attempt public1 compiled variant hash a st))
    (w : World) (r : Result Outcome)
    (finished : (run fuel coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k next_OPEN prove_OPEN w).status = .finished r) :
    prover.retry_attempt coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash nonce_store next_attempt k = r := by
  exact PV_EVH_WorldRecursion.fixed_finished_recursive (S := State T0) (A := Outcome)
    (fun (st,c,i) => body coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i next_OPEN prove_OPEN)
    (fun (st,c,i) => sourceBody coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i)
    (fun (st,c,i) => prover.retry_attempt coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i)
    (by
      rintro ⟨st,c,i⟩
      rw [PV_EVH_RetrySource.source_unfold coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i]
      congr 1
      funext cf
      cases cf with
      | done a => rfl
      | cont next => rcases next with ⟨st,c,i⟩; rfl)
    (fun (st,c,i) => body_fixed coreopsfunctionFnMutT0TupleUsizeResultStateOnlyAttemptSecretsErrorInst public1 compiled variant hash st c i next_OPEN prove_OPEN next_fixed prove_fixed)
    fuel (nonce_store,next_attempt,k) w r finished

#print axioms run_fixed
end PV_EVH_RetryRun
