import R1Z.ProverRw18ContextCaller
import R1Z.PV_RW_DataPartsIff
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextData
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
variable [ExternalTypes]

-- The new loop-context proof is consumed in the complete body criterion.
-- V163's two comparisons and the sibling's source identity remain arguments.
theorem refinement (ops : ExternalFuns) (extracted : ProverRw18ContextJoin.Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted =
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops))
    {S : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce=ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error))
    (proof_bytes : PV_RW_DataProduct.observe PV_RW_DataProduct.first
        (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
          store pub compiled v hash binding digest attempt s)) =
      PV_RW_DataProduct.observe PV_RW_DataProduct.first model)
    (audit_data : PV_RW_DataProduct.observe PV_RW_DataProduct.second
        (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
          store pub compiled v hash binding digest attempt s)) =
      PV_RW_DataProduct.observe PV_RW_DataProduct.second model) :
    ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  rw [ProverRw18ContextCaller.caller ops extracted source_law context_identity]
  apply ProverRwP6BodyData.refinement_of_data (PV_RW_CombinedBodyData.closed ops)
    store pub compiled v hash binding digest attempt s after accepted reservation model
  exact PV_RW_DataProduct.joint _ model proof_bytes audit_data

#print axioms refinement
end R1Z.ProverRw18ContextData
