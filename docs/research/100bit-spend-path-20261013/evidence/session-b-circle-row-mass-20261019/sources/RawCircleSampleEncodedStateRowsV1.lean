import RawCircleSampleActualSuccessModelV2
import AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleEncodedStateRowsV1

open RawCircleSamplePointwiseModelV1
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SourceDuplexStep

/-- For either of the two actual wrapper rows, its successful emitted point
    has exactly the R0P model coordinates at the state encoded in the input
    block. This identifies the actual row output with the model point while
    keeping the row numbering explicit (`First`/`Second`). -/
theorem actual_row_output_matches_model (s : State)
    (row : r0_transcript.CircleRow) :
    ∃ p : circle.SecureCirclePoint,
      sampler.circle_sample (encodeState s) row = .ok p ∧
      actualWideCoordinates p = (modelPoint row s).val := by
  obtain ⟨p, hout, _hcircle⟩ :=
    RawCircleSampleActualPolicyUnconditionalV1.circle_sample_total_on_circle
      (encodeState s) row
  obtain ⟨q, hq, _hqcanonical, hcoords⟩ :=
    RawCircleSampleActualSuccessModelV1.circle_success_has_sample_and_model
      (encodeState s) row p hout
  refine ⟨p, hout, ?_⟩
  rw [state_roundtrip] at hcoords
  exact hcoords

/-- The actual first-row result is the retained row-25 circle sample. -/
theorem actual_row25_output_matches_model (s : State) :
    ∃ p : circle.SecureCirclePoint,
      sampler.circle_sample (encodeState s) .First = .ok p ∧
      actualWideCoordinates p = (R0P.SemSource.circleSample0 s).val := by
  simpa [modelPoint] using actual_row_output_matches_model s .First

/-- The actual second-row result is the retained row-26 circle sample. -/
theorem actual_row26_output_matches_model (s : State) :
    ∃ p : circle.SecureCirclePoint,
      sampler.circle_sample (encodeState s) .Second = .ok p ∧
      actualWideCoordinates p = (R0P.SemSource.circleSample1 s).val := by
  simpa [modelPoint] using actual_row_output_matches_model s .Second

#print axioms actual_row_output_matches_model
#print axioms actual_row25_output_matches_model
#print axioms actual_row26_output_matches_model

end RawCircleSampleEncodedStateRowsV1
end AspisR1CircleSampleWrapper
