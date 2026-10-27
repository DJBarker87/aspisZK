import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Continue038
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


/-- No branch is discarded; the continuation is named rather than existential. -/
theorem equation {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (proof_account : T0) :
    RealR1_client.prove_for_proof_accounts (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (public1 := public1) (compiled := compiled) (hash := hash) (nonce_store := nonce_store) (proof_account := proof_account) =
      (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account >>= fun out => continueAfter (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (public1 := public1) (compiled := compiled) (hash := hash) (nonce_store := nonce_store) (proof_account := proof_account) out) := by
  rw [RealR1_client.prove_for_proof_accounts]
  rfl

/-- Exact successful transition to the source suffix. The guard is not
asserted for native fixtures. -/
theorem success {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (proof_account : T0) (out : Payload (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account))
    (h : (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account) = .ok out) :
    RealR1_client.prove_for_proof_accounts (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (public1 := public1) (compiled := compiled) (hash := hash) (nonce_store := nonce_store) (proof_account := proof_account) = continueAfter (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (public1 := public1) (compiled := compiled) (hash := hash) (nonce_store := nonce_store) (proof_account := proof_account) out := by
  rw [equation, h]
  rfl

/-- Exact failure truncation, without reducing the suffix. -/
theorem failure {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (proof_account : T0) (e : Error)
    (h : (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account) = .fail e) :
    RealR1_client.prove_for_proof_accounts (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (public1 := public1) (compiled := compiled) (hash := hash) (nonce_store := nonce_store) (proof_account := proof_account) = .fail e := by
  rw [equation, h]
  rfl

/-- Divergence does not enter the suffix. -/
theorem diverges {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (proof_account : T0)
    (h : (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account) = .div) :
    RealR1_client.prove_for_proof_accounts (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (public1 := public1) (compiled := compiled) (hash := hash) (nonce_store := nonce_store) (proof_account := proof_account) = .div := by
  rw [equation, h]
  rfl

#print axioms continueAfter
#print axioms equation
#print axioms success
#print axioms failure
#print axioms diverges
end R1Z.PV_RE_Continue038
