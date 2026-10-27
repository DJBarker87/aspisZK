import R1Z.PV_RE_DictSuffix037
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix038
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



end R1Z.PV_RE_DictSuffix038
pv_dict_congr ProverRwFull.RealR1_client.prove_for_proof_accounts
pv_dict_congr R1Z.PV_RE_DictSuffix038.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.RealR1_client.prove_for_proof_accounts
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix038.continueAfter
