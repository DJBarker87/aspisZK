import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee000
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `RealR1_client.prove_for_proof_accounts` (callee `prover.prove_masked_retrying_with`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {T0 : Type} (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst :
  core.ops.function.FnMut T0 Std.Usize (Array Std.U8 32#usize)) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (nonce_store :
  aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) (proof_account : T0) :
  ∃ next, RealR1_client.prove_for_proof_accounts (T0 := T0) (coreopsfunctionFnMutT0TupleUsizeArrayU832Inst := coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) (public1 := public1) (compiled := compiled) (hash := hash) (nonce_store := nonce_store) (proof_account := proof_account) =
    (prover.prove_masked_retrying_with
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError
      coreopsfunctionFnMutT0TupleUsizeArrayU832Inst) public1 compiled
      transport.Variant.S2 hash nonce_store proof_account >>= next) := by
  unfold RealR1_client.prove_for_proof_accounts
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee000
