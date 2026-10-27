import R1Z.ProverRw19CanonicalAuditCriterion
import R1Z.ProverRw19CanonicalAuditRefinement
import R1Z.ProverRw19MathematicalAssembly
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19AssemblyCallerIff
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
variable [ExternalTypes]

-- Exact residual criterion for a specified mathematical serialization output.
-- Its caller-input-to-fields construction and proof-byte equation remain open.
theorem criterion (ops : ExternalFuns)
    (P_source_p6 : ops.op223 =
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops))
    {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce=ok (accepted,after))
    (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) :
    ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after
          (ProverRw19MathematicalAssembly.output fields queries slots) ↔
      PV_RW_DataProduct.observe PV_RW_DataProduct.first
        (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
          store pub compiled v hash binding digest attempt s)) =
        ProverRw19MathematicalAssembly.proofBytes fields queries slots := by
  rw [ProverRw19P6Caller.caller ops P_source_p6]
  apply ProverRw19CanonicalAuditCriterion.result_iff
  · exact ProverRwP6BodyStore.writeback (PV_RW_CombinedBodyData.closed ops)
      store pub compiled v hash binding digest attempt s after accepted reservation
  · exact ProverRw19AuditCaller.good (PV_RW_CombinedBodyData.closed ops)
      store pub compiled v hash binding digest attempt s

#print axioms criterion
end R1Z.ProverRw19AssemblyCallerIff
