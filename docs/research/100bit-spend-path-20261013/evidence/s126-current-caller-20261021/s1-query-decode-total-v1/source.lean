import S1OwnedQueryDecoderInstallationV1
import S1OwnedQueryPairsFixedModelV1
set_option autoImplicit false
namespace AspisS1QueryDecodeTotal
open Aeneas Aeneas.Std Result
open AspisS1OwnedQueryPairs AspisS1OwnedQueryPairs.Model
open AspisR1CurrentCaller.BorrowedClaimPrepared
abbrev ScheduleResult := core.result.Result Query31ConcreteMaterializedSchedule.QueryOutput
  Query31ConcreteMaterializedSchedule.ScheduleQueryError

def scheduleValue : NativeResult → ScheduleResult
  | .Ok out => .Ok out
  | .Err e => .Err (Query31ConcreteMaterializedSchedule.adaptQueryError (toOldError e))

theorem adapt_ok (r : NativeResult) :
    Query31ConcreteMaterializedSchedule.adaptScanResult (adapt (ok r))=ok (scheduleValue r) := by
  cases r <;> rfl

/-- TOTAL concrete decoder field used by preparation. Rejection remains a
native Err result; no accepted-only condition or successful child is supplied. -/
theorem closed_decode_total (blocks advances : Blocks) :
    ∃ (sf : OwnedScan) (selected : Block),
      closedHashQueries.decode blocks advances=ok (scheduleValue (finishValue sf selected)) ∧ Valid sf := by
  obtain ⟨sf,selected,called,walk,valid,model,meaning⟩ :=
    reference_total_fixed blocks advances (AspisV8R19.SqueezeOracleBridge.decodeState
      (atBlock advances 7#usize (by decide)))
  refine ⟨sf,selected,?_,valid⟩
  rw [AspisS1OwnedQueryDecoderInstallation.closed_decoder_eq_owned]
  unfold AspisS1OwnedQueryDecoderInstallation.ownedDecode
  rw [called,adapt_ok]

#print axioms closed_decode_total
end AspisS1QueryDecodeTotal
