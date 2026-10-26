import R1Z.ProverRw19OriginalBodyAudit
import R1Z.ProverRw19MathematicalAssembly
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19MathematicalDataIff
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
variable [ExternalTypes] [ExternalFuns]

-- Exact data criterion for the independent mathematical serialization output.
-- The deployed caller's mathematical fields/queries/slots construction remains
-- open; these arguments are not obtained by projecting the source result.
theorem criterion {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (binding : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S)
    (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) :
    data (prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s) =
      ProverRw19MathematicalAssembly.output fields queries slots ↔
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (prover.prove_masked_with_attempt store pub compiled v hash context binding attempt s)) =
      ProverRw19MathematicalAssembly.proofBytes fields queries slots := by
  exact ProverRw19OriginalBodyAudit.criterion store pub compiled v hash context binding attempt s
    (ProverRw19MathematicalAssembly.proofBytes fields queries slots)

#print axioms criterion
end R1Z.ProverRw19MathematicalDataIff
