import R1Z.PV_RW_CompressNativeBodyData
import R1Z.PV_RW_DataProduct
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_DataParts
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
open PV_RW_CompressNativeBodyData
variable [ExternalTypes]
-- This decomposes, and does not discharge, V163's missing model comparison.
theorem refinement_of_parts (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error))
    (proof_data : PV_RW_DataProduct.observe PV_RW_DataProduct.first
      (data (ProverRwP6BodyStore.execute (closed ops) store pub compiled v hash binding digest attempt s))=
      PV_RW_DataProduct.observe PV_RW_DataProduct.first model)
    (audit_data : PV_RW_DataProduct.observe PV_RW_DataProduct.second
      (data (ProverRwP6BodyStore.execute (closed ops) store pub compiled v hash binding digest attempt s))=
      PV_RW_DataProduct.observe PV_RW_DataProduct.second model) :
    ProverRwP6BodyStore.execute (source ops)
      store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  exact PV_RW_CompressNativeBodyData.refinement_of_data ops
    store pub compiled v hash binding digest attempt s after accepted reservation model
    (PV_RW_DataProduct.joint _ model proof_data audit_data)
#print axioms refinement_of_parts
end R1Z.PV_RW_DataParts
