import R1Z.ProverRw19AuditSource
import R1Z.ProverRw19AuditData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19OriginalBodyAudit
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
open ProverRw19AuditData
variable [ExternalTypes] [ExternalFuns]

-- A direct theorem about the original emitted body, before any compression
-- replacement. The model byte function remains independently specified.
-- No source law, context identity, reservation success, or successful-return
-- assumption is needed to show that the audit follows the byte equation.
theorem criterion {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S)
    (modelBytes : Result ByteStatus) :
    data (prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s) =
      attachAudit modelBytes ↔
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s)) =
      modelBytes := by
  constructor
  · intro same
    rw [same, bytes]
  · intro P_proof_bytes
    exact data_of_bytes _ modelBytes
      (ProverRw19AuditSource.body store pub compiled v hash context binding attempt s)
      P_proof_bytes

#print axioms criterion
end R1Z.ProverRw19OriginalBodyAudit
