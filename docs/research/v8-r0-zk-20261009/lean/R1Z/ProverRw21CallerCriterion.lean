import R1Z.ProverRw21ModelObservations
import R1Z.ProverRw18ContextDataIff
import R1Z.ProverRw19AuditCaller
import R1Z.ProverRw19P6ContextIdentity
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21CallerCriterion
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
variable [ExternalTypes]

/-- Exact original caller criterion for the independently constructed model.
The original op223 association and byte equation remain named obligations.
This theorem does not supply the missing deployed protocol construction. -/
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
    (protocol : ProverRw21ModelObservations.Protocol) :
    ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s =
      ProverRwBodyCandidateData.withState after (ProverRw21ModelInstance protocol) ↔
    PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
        store pub compiled v hash binding digest attempt s)) =
      ProverRw21ModelObservations.proofBytes protocol := by
  rw [ProverRw18ContextDataIff.criterion ops _ P_source_p6
    (ProverRw19P6ContextIdentity.identity ops) store pub compiled v hash binding digest attempt
    s after accepted reservation (ProverRw21ModelInstance protocol),ProverRw21ModelObservations.bytes]
  constructor
  · intro h
    exact h.1
  · intro hb
    refine ⟨hb,?_⟩
    change PV_RW_DataProduct.observe PV_RW_DataProduct.second
      (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
        store pub compiled v hash binding digest attempt s)) =
      PV_RW_DataProduct.observe PV_RW_DataProduct.second
        (ProverRw19AuditData.attachAudit (ProverRw21ModelObservations.proofBytes protocol))
    exact ProverRw19AuditData.audit_of_bytes _ _
      (ProverRw19AuditCaller.good (PV_RW_CombinedBodyData.closed ops)
        store pub compiled v hash binding digest attempt s) hb

#print axioms criterion
end R1Z.ProverRw21CallerCriterion
