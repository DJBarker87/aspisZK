import R1Z.PV_RW_CombinedCompression
import R1Z.PV_RW_CompressClosedBodyData
import R1Z.ProverRwP6BodyData
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CombinedBodyData
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyDataCriterion
variable [ExternalTypes]

@[reducible] def source (ops : ExternalFuns) : ExternalFuns :=
  {PV_CurrentScaleInstall.selected ops with op223 := PV_RW_CombinedCompression.compress ops}

@[reducible] def closed (ops : ExternalFuns) : ExternalFuns :=
  {PV_CurrentScaleInstall.selected ops with op223 := PV_RW_CompressClosed.owned}

theorem dictionaries (ops : ExternalFuns) : source ops = closed ops := by
  have same : PV_RW_CombinedCompression.compress ops =
      PV_RW_CompressClosed.owned := by
    funext tag values lambda
    exact PV_RW_CombinedCompression.owned ops tag values lambda
  dsimp only [source,closed]
  rw [same]

theorem caller (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S) :
    ProverRwP6BodyStore.execute (source ops)
      store pub compiled v hash binding digest attempt s =
    ProverRwP6BodyStore.execute (closed ops)
      store pub compiled v hash binding digest attempt s := by
  rw [dictionaries]

-- The original Rust whole-helper association remains open.
-- V163's entire proof/audit data equation is retained visibly. The exact
-- source-model compression replacement is consumed rather than re-assumed.
theorem refinement_of_data (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error))
    (whole_data : data (ProverRwP6BodyStore.execute (closed ops)
      store pub compiled v hash binding digest attempt s)=model) :
    ProverRwP6BodyStore.execute (source ops)
      store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  rw [caller]
  exact ProverRwP6BodyData.refinement_of_data (closed ops)
    store pub compiled v hash binding digest attempt s after accepted reservation model whole_data
#print axioms dictionaries
#print axioms caller
#print axioms refinement_of_data
end R1Z.PV_RW_CombinedBodyData
