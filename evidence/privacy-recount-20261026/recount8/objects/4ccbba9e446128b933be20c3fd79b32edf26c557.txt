import R1Z.PV_Join_PublicDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicCaller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion
abbrev native := PV_Join_PublicInstall.native
/-- Preserve the complete P8 installation; reapplying all P6 selectors would
replace op255 by its earlier partial S1/S2 implementation. -/
abbrev selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :=
  @ProverRwOuterGuardLeaves.selected (native base) (PV_Join_PublicInstall.selected base ops)
abbrev execute (base : ExternalTypes) (ops : @ExternalFuns (native base)) :=
  @ProverRwBodyNativeWideInstall.execute (native base) (selected base ops)
-- Same complete Result, reservation premise and whole proof/audit data equation.
theorem refinement_of_data (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    letI : ExternalTypes := native base
    ∀ {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error)),
    data (execute base ops store pub compiled v hash binding digest attempt s)=model →
      execute base ops store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  letI : ExternalTypes := native base
  intro S store pub compiled v hash binding digest attempt s after accepted reservation model same
  unfold execute selected at same ⊢
  rw [PV_Join_PublicDictionary.dictionary] at same ⊢
  apply eq_of_data after
  · exact ProverRwBodyReservationTransport.body_writeback
      (@PV_TraceValueInstall.selected (native base) (PV_Join_PublicDictionary.raw base ops))
      store pub compiled v hash binding digest attempt s after accepted reservation
  · exact ProverRwBodyCandidateData.keeps_withState after model
  · rw [ProverRwBodyCandidateData.data_withState]
    exact same

/-- Complete Result independence from the supplied raw equality callback. -/
theorem caller_callback_removed (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (callback : PV_Join_PublicInstall.Late base → PV_Join_PublicInstall.Late base → Result Bool) :
    letI : ExternalTypes := native base
    ∀ {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s : S),
    execute base {ops with op229 := callback} store pub compiled v hash binding digest attempt s =
    execute base ops store pub compiled v hash binding digest attempt s := by
  letI : ExternalTypes := native base
  intro S store pub compiled v hash binding digest attempt s
  unfold execute selected
  rw [PV_Join_PublicInstall.callback_removed]
#print refinement_of_data
#print axioms refinement_of_data
#print axioms caller_callback_removed
end R1Z.PV_Join_PublicCaller
