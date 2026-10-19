import RawCircleSamplePointwiseModelV10
import AspisR1CircleSampleWrapper.RawCircleSampleActualSamplerCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualSuccessModelV1

open RawCircleSamplePointwiseModelV1
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SqueezeOracleBridge

/-- A successful emitted point implies that the actual wrapper's QM31 sampler
    succeeded; its result is canonical and the point's coordinates are the
    corresponding R0P model sample. -/
theorem circle_success_has_sample_and_model
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow)
    (p : circle.SecureCirclePoint)
    (hout : sampler.circle_sample block row = .ok p) :
    ∃ q : field.QM31,
      sampler.qm31_sample block = .ok q ∧
      Canonical (toR72QM q) ∧
      actualWideCoordinates p = (modelPoint row (decodeState block)).val := by
  cases hsample : sampler.qm31_sample block with
  | ok q =>
      refine ⟨q, rfl, ?_, ?_⟩
      · exact RawCircleSampleActualSamplerCanonicalV1.successful_sample_toR72_canonical
          block q hsample
      · have hcanonical :=
          RawCircleSampleActualSamplerCanonicalV1.successful_sample_toR72_canonical
            block q hsample
        exact actual_sample_coordinates_eq_model block row q p hsample hcanonical hout
  | fail e =>
      simp [sampler.circle_sample, hsample] at hout
  | div =>
      simp [sampler.circle_sample, hsample] at hout

#print axioms circle_success_has_sample_and_model
end RawCircleSampleActualSuccessModelV1
end AspisR1CircleSampleWrapper
