import R1Z.ProverRw19P6Caller
import R1Z.ProverRw18ContextData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19P6DataIff
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
variable [ExternalTypes]

-- V163 remains the conjunction of two observation equations. This supplies
-- neither equation and does not define the required mathematical whole model.
-- The concrete P6 identity eliminates only rw18's context_identity argument.
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
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error))
 :
    ProverRwP6BodyStore.execute (ProverRw18ContextJoin.original ops)
      store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model ↔
      (PV_RW_DataProduct.observe PV_RW_DataProduct.first
        (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
          store pub compiled v hash binding digest attempt s)) =
        PV_RW_DataProduct.observe PV_RW_DataProduct.first model ∧
       PV_RW_DataProduct.observe PV_RW_DataProduct.second
        (data (ProverRwP6BodyStore.execute (PV_RW_CombinedBodyData.closed ops)
          store pub compiled v hash binding digest attempt s)) =
        PV_RW_DataProduct.observe PV_RW_DataProduct.second model) := by
  rw [ProverRw19P6Caller.caller ops P_source_p6]
  apply PV_RW_DataPartsIff.exact_criterion
  exact ProverRwP6BodyStore.writeback (PV_RW_CombinedBodyData.closed ops)
    store pub compiled v hash binding digest attempt s after accepted reservation

#print axioms criterion
end R1Z.ProverRw19P6DataIff
