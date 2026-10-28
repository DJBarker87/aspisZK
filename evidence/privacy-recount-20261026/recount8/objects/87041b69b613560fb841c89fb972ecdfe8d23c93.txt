import R1Z.ProverRw19P6Caller
import R1Z.ProverRw19AuditCaller
import R1Z.PV_RW_DataPartsIff
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19CanonicalAuditRefinement
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
variable [ExternalTypes]

-- Conditional whole-body refinement with a canonical mathematical audit.
-- No concrete whole-model byte function or byte equality is supplied here.
-- P_source_p6 and P_proof_bytes remain exact named open obligations.
theorem refinement (ops : ExternalFuns)
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
    (modelBytes : Result ProverRw19AuditData.ByteStatus)
    (P_proof_bytes : PV_RW_DataProduct.observe PV_RW_DataProduct.first
        (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
          store pub compiled v hash binding digest attempt s)) = modelBytes) :
    ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after (ProverRw19AuditData.attachAudit modelBytes) := by
  rw [ProverRw19P6Caller.caller ops P_source_p6]
  apply ProverRwP6BodyData.refinement_of_data (PV_RW_CombinedBodyData.closed ops)
    store pub compiled v hash binding digest attempt s after accepted reservation
      (ProverRw19AuditData.attachAudit modelBytes)
  apply ProverRw19AuditData.data_of_bytes
  · exact ProverRw19AuditCaller.good (PV_RW_CombinedBodyData.closed ops)
      store pub compiled v hash binding digest attempt s
  · exact P_proof_bytes

#print axioms refinement
end R1Z.ProverRw19CanonicalAuditRefinement
