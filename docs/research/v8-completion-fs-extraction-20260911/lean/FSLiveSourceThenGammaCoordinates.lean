import FSLiveSourceThenGammaV7Decode
import SameBodyOODSourcePrimitives

/-!
# Canonical coordinates from a successful source/gamma trace

This is a consumer of the public component-elimination theorem.  It does not
re-run the sampler: the component theorem supplies the concrete first and
second traces, while `SameBodyOODSourcePrimitives` supplies their canonical
coordinate decoding.  The executable `fromSampled` constructor is retained as
a fail-closed success-or-rejection alternative.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.FSLiveSourceThenGammaCoordinates

open AspisV8Completion.FSLiveSourceThenGammaV7Decode
open AspisV8Completion.SameBodyOODSourcePrimitives
open AspisV8Completion.SameBodyOODData
open AspisV8Completion.FSLiveOODV7Decode
open AspisV8Completion.FSOODSampler
open AspisV8Completion.FSOracleExecution
open AspisV8Completion.FSBoundedTranscript
open FSV7OODBodyScript
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSLiveOODV7Decode.Tape
abbrev Transcript := FSLiveOODV7Decode.Transcript
abbrev Point := FSLiveOODV7Decode.Point
abbrev OODResult := FSLiveSourceThenGammaV7Decode.OODResult
abbrev Gamma := FSLiveSourceThenGammaV7Decode.Gamma
abbrev K := SameBodyOODData.K

noncomputable section

theorem successful_source_coordinates_or_data {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (tape : Tape) (start : Transcript)
    (out : OODResult) (gamma : Gamma)
    (success :
      (sourceGammaTrace firstWork secondWork body tape start).outcome =
        some (.ok (out, gamma))) :
    (∃ x0 y0 x1 y1 : K,
      AspisK1.V7Tag73SecureCircleMap.decodeTagQM31ExactLE out.first.x = some x0 ∧
      AspisK1.V7Tag73SecureCircleMap.decodeTagQM31ExactLE out.first.y = some y0 ∧
      AspisK1.V7Tag73SecureCircleMap.decodeTagQM31ExactLE out.second.x = some x1 ∧
      AspisK1.V7Tag73SecureCircleMap.decodeTagQM31ExactLE out.second.y = some y1) ∧
    (fromSampled out gamma body = none ∨
      ∃ data, fromSampled out gamma body = some data ∧ data.Checked) := by
  rcases successful_trace_components firstWork secondWork body tape start out gamma
      success with
    ⟨first, second, hfirst, hsecond, hfirstResult, hsecondResult,
      hfirstConcrete, hsecondShape⟩
  rcases hsecondShape with ⟨firstPoint, hfirstPointResult, hsecondConcrete⟩
  have firstResult : first.result = .ok out.first := hfirstResult
  have secondResult : second.result = .ok out.second := hsecondResult
  have firstTraceResult : (circleTrace tape 3 start).result = .ok out.first := by
    simpa [hfirstConcrete] using firstResult
  have firstSuccessful : SuccessfulCircle out.first first.attempts := by
    rw [hfirstConcrete]
    exact circleTrace_successful tape 3 start out.first firstTraceResult
  have firstCoordinates := successfulCircle_coordinates out.first first.attempts
    firstSuccessful
  let afterFirst := absorb tape
    { digest := (circleTrace tape 3 start).final.digest,
      oracle := (run tape (firstWork firstPoint)
        (circleTrace tape 3 start).final.oracle).2 }
    62 (0 :: FSV8OODBodyScript.answerBytes body 0)
  have secondSuccessful : SuccessfulDistinct firstPoint out.second
      second.rounds := by
    have secondTraceResult :
        (distinctTrace firstPoint tape 3 afterFirst).result = .ok out.second := by
      simpa [hsecondConcrete, afterFirst] using secondResult
    rw [hsecondConcrete]
    simpa [hsecondConcrete, afterFirst] using
      (distinctTrace_successful firstPoint tape 3 afterFirst out.second
        secondTraceResult)
  have secondChronological : ChronologicalDistinct tape afterFirst
      second.rounds second.final := by
    simpa [hsecondConcrete, afterFirst] using
      (distinctTrace_chronological firstPoint tape 3 afterFirst)
  have secondCoordinates := successfulDistinct_coordinates firstPoint out.second
    tape secondChronological secondSuccessful
  rcases firstCoordinates with ⟨x0, y0, hx0, hy0⟩
  rcases secondCoordinates with ⟨x1, y1, hx1, hy1⟩
  refine ⟨⟨x0, y0, x1, y1, hx0, hy0, hx1, hy1⟩, ?_⟩
  cases sampled : fromSampled out gamma body with
  | none => exact Or.inl rfl
  | some data =>
      refine Or.inr ⟨data, ?_, ?_⟩
      · rfl
      · exact fromSampled_checked out gamma body data sampled

#print axioms successful_source_coordinates_or_data

end
end AspisV8Completion.FSLiveSourceThenGammaCoordinates
