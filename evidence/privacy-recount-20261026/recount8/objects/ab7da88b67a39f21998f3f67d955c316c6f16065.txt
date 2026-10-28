import R1Z.ProverRw19AuditSource
import R1Z.ProverRw19AuditData
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_NativeAudit
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19AuditValue
variable [ExternalTypes]
/-- All successful audit values of the actual emitted attempt entry are canonical.
No fixture success, source byte model, or IO/effect interpretation is assumed. -/
theorem native_attempt_good (ops : ExternalFuns)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    letI : ExternalFuns := ops
    Good (prover.prove_masked_attempt pub compiled v hash attempt store) := by
  letI : ExternalFuns := ops
  unfold prover.prove_masked_attempt
  repeat' first
    | exact ProverRw19AuditSource.body _ _ _ _ _ _ _ _ _
    | exact residual _ _
    | apply bind_good; intro x
    | dsimp only [Aeneas.Std.uncurry]
    | split

/-- Complete error/failure/divergence-preserving data equality follows from the
independent mathematical byte-result equation. That byte equation remains open. -/
theorem data_of_model_bytes (ops : ExternalFuns)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (store : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore)
    (modelBytes : Result ProverRw19AuditData.ByteStatus) :
    letI : ExternalFuns := ops
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (ProverRwBodyDataCriterion.data (prover.prove_masked_attempt pub compiled v hash attempt store)) = modelBytes →
    ProverRwBodyDataCriterion.data (prover.prove_masked_attempt pub compiled v hash attempt store) =
      ProverRw19AuditData.attachAudit modelBytes := by
  letI : ExternalFuns := ops
  intro bytes
  exact ProverRw19AuditData.data_of_bytes _ modelBytes
    (native_attempt_good ops pub compiled v hash attempt store) bytes

#print axioms native_attempt_good
#print axioms data_of_model_bytes
end R1Z.PV_Join_NativeAudit
