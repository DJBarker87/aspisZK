import R1Z.ProverRwBodyReservationTransport
import R1Z.ProverRwSuccessBodyInterpretation
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyCandidateStore
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore
variable [ExternalTypes]
-- Compose the proved guard leaves with the success-body candidate. Native
-- dictionary and whole proof-output adequacy are separate obligations.
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected (ProverRwSuccessBodyInterpretation.selected ops)

theorem points (ops : ExternalFuns) (alpha : Array aspis_core.field.QM31 10#usize) :
    (selected ops).op118 alpha=
      ProverRwSuccessPointsSource.state_only_prefix.state_only_statement_points alpha := rfl

theorem writeback (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce=.ok (accepted,after)) :
    letI : ExternalFuns := selected ops
    Keeps after (prover.prove_masked_with_attempt store pub compiled v hash
      (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt s) :=
  ProverRwBodyReservationTransport.body_writeback
    (ProverRwSuccessBodyInterpretation.selected ops) store pub compiled v hash
      binding digest attempt s after accepted reservation
#print axioms points
#print axioms writeback
end R1Z.ProverRwBodyCandidateStore
