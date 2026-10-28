import R1Z.ProverRw19AuditSource
import R1Z.ProverRw19AuditData
import R1Z.ProverRwP6BodyStore
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19AuditCaller
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19AuditValue ProverRw19AuditData
open ProverRwBodyDataCriterion
variable [ExternalTypes]

theorem good (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    Good (ProverRwP6BodyStore.execute ops store pub compiled v hash binding digest attempt s) :=
  @ProverRw19AuditSource.body _ (ProverRwP6BodyStore.selected ops) S store pub compiled v hash
    (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt s

-- The exact full audit equation is a consequence of the named byte equation,
-- once the mathematical model returns the canonical audit on success.
-- modelBytes is still a parameter: this is not the concrete V163 model.
theorem audit (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S)
    (modelBytes : Result ByteStatus)
    (P_proof_bytes : PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (ProverRwP6BodyStore.execute ops store pub compiled v hash binding digest attempt s)) = modelBytes) :
    PV_RW_DataProduct.observe PV_RW_DataProduct.second
      (data (ProverRwP6BodyStore.execute ops store pub compiled v hash binding digest attempt s)) =
        PV_RW_DataProduct.observe PV_RW_DataProduct.second (attachAudit modelBytes) :=
  audit_of_bytes _ modelBytes (good ops store pub compiled v hash binding digest attempt s) P_proof_bytes

#print axioms good
#print axioms audit
end R1Z.ProverRw19AuditCaller
