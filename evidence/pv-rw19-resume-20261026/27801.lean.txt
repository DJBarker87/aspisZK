import R1Z.ProverRw19CanonicalAuditCriterion
import R1Z.ProverRw19AuditCaller
import R1Z.ProverRw18ContextJoin
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19OriginalAuditCriterion
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
open ProverRw19AuditData
variable [ExternalTypes]

-- Works on the original dictionary. No compression replacement or source law
-- is assumed. The source byte equation below is still an OPEN obligation;
-- moving it to the closed P6 dictionary requires the separately named law.
theorem criterion (ops : ExternalFuns)
    {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce=ok (accepted,after))
    (modelBytes : Result ByteStatus) :
    ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after (attachAudit modelBytes) ↔
      PV_RW_DataProduct.observe PV_RW_DataProduct.first
        (data (ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
          store pub compiled v hash binding digest attempt s)) = modelBytes := by
  apply ProverRw19CanonicalAuditCriterion.result_iff
  · exact ProverRwP6BodyStore.writeback (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s after accepted reservation
  · exact ProverRw19AuditCaller.good (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s

#print axioms criterion
end R1Z.ProverRw19OriginalAuditCriterion
