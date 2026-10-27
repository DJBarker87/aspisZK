import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix038
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `RealR1_client.prove_for_proof_accounts`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (proof_account : T0) (out : Payload (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account)) : Result ((core.result.Result prover.RetriedProof verifier.Error) ×
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) := do
  let (r, nonce_store1) := out
  ok (r, nonce_store1)



end R1Z.PV_RE_NoCatchSuffix038
pv_no_catch_binds ProverRwFull.RealR1_client.prove_for_proof_accounts
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix038.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix039
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once`.
Recursive calls remain the original extracted calls. -/
def continueAfter {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (c : RealR1_client.prove_for_proof_accounts.closure T0) (i : Std.Usize) (out : Payload (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst c i)) : Result ((core.result.Result
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets verifier.Error) ×
    (RealR1_client.prove_for_proof_accounts.closure T0)) := do
  let (r, c1, call_mut_back) := out
  ok (r, call_mut_back c1)


end R1Z.PV_RE_NoCatchSuffix039
pv_no_catch_binds ProverRwFull.RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeResultStateOnlyAttemptSecretsError.call_once
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix039.continueAfter
