import R1Z.PV_RunJoin_BindCongruence
import R1Z.PV_RunJoin_BodyProjection
import R1Z.PV_RunJoin_CallerProjection
import R1Z.PV_RunJoin_ConsumedEvent
import R1Z.PV_RunJoin_ContinuationProjection
import R1Z.PV_RunJoin_DictionaryIdentity
import R1Z.PV_RunJoin_EnteredBody
import R1Z.PV_RunJoin_EnteredCallback
import R1Z.PV_RunJoin_EnteredCaller
import R1Z.PV_RunJoin_EnteredGuards
import R1Z.PV_RunJoin_FixtureSelectedSources
import R1Z.PV_RunJoin_Follows
import R1Z.PV_RunJoin_GuardProjection
import R1Z.PV_RunJoin_InstalledEndpoint
import R1Z.PV_RunJoin_InstalledFamily
import R1Z.PV_RunJoin_InstalledTransport
import R1Z.PV_RunJoin_LedgerBoundary
import R1Z.PV_RunJoin_LedgerBoundaryEffects
import R1Z.PV_RunJoin_LedgerBoundaryLedger
import R1Z.PV_RunJoin_LedgerBoundarySource
import R1Z.PV_RunJoin_LedgerConstructor
import R1Z.PV_RunJoin_LedgerEndpoint
import R1Z.PV_RunJoin_LedgerPublicEntry
import R1Z.PV_RunJoin_LedgerPublicShape
import R1Z.PV_RunJoin_LedgerSourceBody
import R1Z.PV_RunJoin_LedgerSourceProjection
import R1Z.PV_RunJoin_MapErrInstalled
import R1Z.PV_RunJoin_NativeEffectInterface
import R1Z.PV_RunJoin_NativeEffectTransport
import R1Z.PV_RunJoin_NativeInputTypes
import R1Z.PV_RunJoin_NativePublicReservation
import R1Z.PV_RunJoin_NativeSelectedInputs
import R1Z.PV_RunJoin_NominalCompiledData
import R1Z.PV_RunJoin_NominalLeafData
import R1Z.PV_RunJoin_NominalPublicData
import R1Z.PV_RunJoin_NominalTraceData
import R1Z.PV_RunJoin_OsFailurePure
import R1Z.PV_RunJoin_OsTrace
import R1Z.PV_RunJoin_OsWorld
import R1Z.PV_RunJoin_OsWorldFrames
import R1Z.PV_RunJoin_OsWorldReplay
import R1Z.PV_RunJoin_PublicCarrierFrame
import R1Z.PV_RunJoin_PublicDecision
import R1Z.PV_RunJoin_PublicReservation
import R1Z.PV_RunJoin_ReservationProjection
import R1Z.PV_RunJoin_ReserveClassification
import R1Z.PV_RunJoin_ResidualPrint
import R1Z.PV_RunJoin_SelectedAdmission
import R1Z.PV_RunJoin_SelectedEntry
import R1Z.PV_RunJoin_SelectedErrorPrelude
import R1Z.PV_RunJoin_SelectedOsFailure
import R1Z.PV_RunJoin_SourceSelectionContract
import R1Z.PV_RunJoin_SourceTypes
import R1Z.PV_RunJoin_VariantIdentity
import R1Z.PV_RunJoin_ZeroizingBefore
import R1Z.PV_RunJoin_ZeroizingPrefix
import R1Z.PV_RunJoin_ConsumedEvent
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompleteEventStep
open PV_RunJoin_OsWorld PV_RunJoin_OsTrace
variable {E File Reply Time Worker : Type} [DecidableEq File]

theorem file_consumed (request : Request File) (world next : World E File Reply Time Worker)
    (reply : Reply) (run : fileStep request world = some (reply,next)) :
    ∃ event, world.files[world.fileUsed]? = some event ∧ event.request = request ∧
      event.reply = reply ∧ consumed next =
        {consumed world with files := (consumed world).files ++ [event]} := by
  unfold fileStep at run
  cases position : world.files[world.fileUsed]? with
  | none => simp [position] at run
  | some event =>
    simp only [position] at run
    dsimp only [Bind.bind,Option.bind] at run
    split at run
    next hrequest =>
      cases Option.some.inj run
      exact ⟨event,rfl,hrequest,rfl,PV_RunJoin_ConsumedEvent.file_append world event position⟩
    next => contradiction

theorem time_consumed (world next : World E File Reply Time Worker)
    (outcome : Time) (run : timeStep world = some (outcome,next)) :
    consumed next = {consumed world with times := (consumed world).times ++ [outcome]} := by
  unfold timeStep at run
  cases position : world.time[world.timeUsed]? with
  | none => simp [position] at run
  | some value =>
    simp only [position] at run
    dsimp only [Bind.bind,Option.bind] at run
    cases Option.some.inj run
    exact PV_RunJoin_ConsumedEvent.time_append world outcome position

theorem worker_consumed (world next : World E File Reply Time Worker)
    (outcome : Worker) (run : workerStep world = some (outcome,next)) :
    consumed next = {consumed world with workers := (consumed world).workers ++ [outcome]} := by
  unfold workerStep at run
  cases position : world.workers[world.workerUsed]? with
  | none => simp [position] at run
  | some value =>
    simp only [position] at run
    dsimp only [Bind.bind,Option.bind] at run
    cases Option.some.inj run
    exact PV_RunJoin_ConsumedEvent.worker_append world outcome position

#print axioms file_consumed
#print axioms time_consumed
#print axioms worker_consumed
end R1Z.PV_RunJoin_CompleteEventStep

/- Focused final audit of retained cached declarations; not a frozen dependency-closure replay. -/
#print axioms R1Z.PV_RunJoin_AvailableOption.privacy_headline_from_premises_available
#print axioms R1Z.PV_RunJoin_BindCongruence.bind_same
#print axioms R1Z.PV_RunJoin_BindCongruence.if_same
#print axioms R1Z.PV_RunJoin_BodyProjection.body
#print axioms R1Z.PV_RunJoin_CallerProjection.caller
#print axioms R1Z.PV_RunJoin_ConsumedEvent.file_append
#print axioms R1Z.PV_RunJoin_ConsumedEvent.time_append
#print axioms R1Z.PV_RunJoin_ConsumedEvent.worker_append
#print axioms R1Z.PV_RunJoin_ContinuationProjection.after_reserve
#print axioms R1Z.PV_RunJoin_DictionaryIdentity.map_error
#print axioms R1Z.PV_RunJoin_DictionaryIdentity.parametric
#print axioms R1Z.PV_RunJoin_EnteredBody.body
#print axioms R1Z.PV_RunJoin_EnteredCallback.entered
#print axioms R1Z.PV_RunJoin_EnteredCaller.caller
#print axioms R1Z.PV_RunJoin_EnteredGuards.guarded
#print axioms R1Z.PV_RunJoin_FixtureSelectedSources.both_source
#print axioms R1Z.PV_RunJoin_Follows.bind_common
#print axioms R1Z.PV_RunJoin_Follows.continuation
#print axioms R1Z.PV_RunJoin_Follows.returned
#print axioms R1Z.PV_RunJoin_GuardProjection.guarded
#print axioms R1Z.PV_RunJoin_InstalledEndpoint.runtime
#print axioms R1Z.PV_RunJoin_InstalledFamily.map_error
#print axioms R1Z.PV_RunJoin_InstalledFamily.public_common
#print axioms R1Z.PV_RunJoin_InstalledTransport.endpoint_row_call
#print axioms R1Z.PV_RunJoin_InstalledTransport.endpoint_transport
#print axioms R1Z.PV_RunJoin_LedgerBoundaryEffects.fault_field
#print axioms R1Z.PV_RunJoin_LedgerBoundaryEffects.fill_field
#print axioms R1Z.PV_RunJoin_LedgerBoundaryLedger.ledger_field
#print axioms R1Z.PV_RunJoin_LedgerBoundarySource.source_fields
#print axioms R1Z.PV_RunJoin_LedgerEndpoint.toPremises
#print axioms R1Z.PV_RunJoin_LedgerPublicEntry.reservation_eq
#print axioms R1Z.PV_RunJoin_LedgerPublicShape.ledger_public
#print axioms R1Z.PV_RunJoin_LedgerSourceBody.provider_frame
#print axioms R1Z.PV_RunJoin_LedgerSourceBody.source_law
#print axioms R1Z.PV_RunJoin_LedgerSourceProjection.caller
#print axioms R1Z.PV_RunJoin_MapErrInstalled.installed
#print axioms R1Z.PV_RunJoin_MapErrInstalled.pure_parametric
#print axioms R1Z.PV_RunJoin_MapErrInstalled.selected
#print axioms R1Z.PV_RunJoin_NativeEffectTransport.file_iff
#print axioms R1Z.PV_RunJoin_NativeEffectTransport.time_iff
#print axioms R1Z.PV_RunJoin_NativeEffectTransport.worker_iff
#print axioms R1Z.PV_RunJoin_NativePublicReservation.decision_eq
#print axioms R1Z.PV_RunJoin_NativePublicReservation.ledger_eq
#print axioms R1Z.PV_RunJoin_NativePublicReservation.public_eq
#print axioms R1Z.PV_RunJoin_NativeSelectedInputs.full_ledger_source
#print axioms R1Z.PV_RunJoin_NativeSelectedInputs.same_selected_compilation
#print axioms R1Z.PV_RunJoin_NominalCompiledData.compiled_roundtrip
#print axioms R1Z.PV_RunJoin_NominalCompiledData.public_snapshot
#print axioms R1Z.PV_RunJoin_NominalCompiledData.semantic_columns
#print axioms R1Z.PV_RunJoin_NominalCompiledData.transition_roundtrip
#print axioms R1Z.PV_RunJoin_NominalLeafData.afterstate_roundtrip
#print axioms R1Z.PV_RunJoin_NominalLeafData.foundation_roundtrip
#print axioms R1Z.PV_RunJoin_NominalLeafData.snapshot_roundtrip
#print axioms R1Z.PV_RunJoin_NominalPublicData.selected_public
#print axioms R1Z.PV_RunJoin_NominalTraceData.outputs_roundtrip
#print axioms R1Z.PV_RunJoin_NominalTraceData.trace_roundtrip
#print axioms R1Z.PV_RunJoin_NominalTraceData.variant_roundtrip
#print axioms R1Z.PV_RunJoin_OsFailurePure.client_map_error
#print axioms R1Z.PV_RunJoin_OsFailurePure.s2_ne
#print axioms R1Z.PV_RunJoin_OsTrace.same_complete_prefix
#print axioms R1Z.PV_RunJoin_OsWorld.file_at
#print axioms R1Z.PV_RunJoin_OsWorld.flush_frame
#print axioms R1Z.PV_RunJoin_OsWorld.time_at
#print axioms R1Z.PV_RunJoin_OsWorld.worker_at
#print axioms R1Z.PV_RunJoin_OsWorldFrames.file_frame
#print axioms R1Z.PV_RunJoin_OsWorldFrames.time_frame
#print axioms R1Z.PV_RunJoin_OsWorldFrames.worker_frame
#print axioms R1Z.PV_RunJoin_OsWorldReplay.replay_entropy
#print axioms R1Z.PV_RunJoin_OsWorldReplay.step_entropy
#print axioms R1Z.PV_RunJoin_PublicCarrierFrame.compiled_injective
#print axioms R1Z.PV_RunJoin_PublicCarrierFrame.native_public_unchanged
#print axioms R1Z.PV_RunJoin_PublicCarrierFrame.public_unchanged
#print axioms R1Z.PV_RunJoin_PublicDecision.common
#print axioms R1Z.PV_RunJoin_PublicDecision.returned
#print axioms R1Z.PV_RunJoin_PublicFailureEndpoint.privacy_headline_public_failure
#print axioms R1Z.PV_RunJoin_PublicReservation.common
#print axioms R1Z.PV_RunJoin_ReservationProjection.after_checks
#print axioms R1Z.PV_RunJoin_ReserveClassification.accepted_clean
#print axioms R1Z.PV_RunJoin_ReserveClassification.rejected_without_error
#print axioms R1Z.PV_RunJoin_SelectedAdmission.toPremises
#print axioms R1Z.PV_RunJoin_SelectedEntry.call
#print axioms R1Z.PV_RunJoin_SelectedEntry.seven_field_erasure
#print axioms R1Z.PV_RunJoin_SelectedErrorPrelude.source_prelude_error
#print axioms R1Z.PV_RunJoin_SelectedOsFailure.selected_error
#print axioms R1Z.PV_RunJoin_SourceBoundary.native_fill_V336
#print axioms R1Z.PV_RunJoin_SourceBoundary.source_V045
#print axioms R1Z.PV_RunJoin_SourceSelectionContract.installed_row
#print axioms R1Z.PV_RunJoin_SourceSelectionContract.selected_public
#print axioms R1Z.PV_RunJoin_VariantIdentity.selected_variant
#print axioms R1Z.PV_RunJoin_ZeroizingBefore.before_returns
#print axioms R1Z.PV_RunJoin_ZeroizingPrefix.type_installed
#print axioms R1Z.ProverRwBodyStore.continuation
