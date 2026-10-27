import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualSamplerCanonicalV1
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualPolicyV2
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualPolicyUnconditionalV1

open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerCirclePolicy

/-- The actual wrapper sampler always returns a canonical R72 parameter: its
    result is a coordinate copy of the public sampler's proven total output. -/
theorem sampler_total_canonical (block : Array Std.U8 32#usize) :
    ∃ q : field.QM31, sampler.qm31_sample block = .ok q ∧ Canonical (toR72QM q) := by
  obtain ⟨qpub, hpub, _, _⟩ :=
    AspisR1PublicPreparation.SamplerTransport.sample_total block
  have hw : sampler.qm31_sample block = .ok (fromPublicQM qpub) := by
    rw [RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public, hpub]
    rfl
  exact ⟨fromPublicQM qpub, hw,
    RawCircleSampleActualSamplerCanonicalV1.successful_sample_toR72_canonical
      block (fromPublicQM qpub) hw⟩

/-- Canonical inputs make the actual wrapper mapper return an ordinary outer
    `.ok`; its exact behavior is the retained R72 source execution. -/
theorem mapper_result_total (q : field.QM31)
    (hq : Canonical (toR72QM q)) :
    ∃ r : core.result.Result circle.SecureCirclePoint circle.CirclePointError,
      circle.secure_ood_circle_point_from_parameter q = .ok r := by
  have hsource :=
    AspisV8R19.SamplerClosureCircleSourceExecution.source_execution (toR72QM q) hq
  cases hr : AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
      (toR72QM q) with
  | fail e =>
      rw [hr] at hsource
      cases hsource
  | div =>
      rw [hr] at hsource
      cases hsource
  | ok out =>
      cases out with
      | Ok p =>
          refine ⟨.Ok (fromR72Point p), ?_⟩
          rw [RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72, hr]
          rfl
      | Err e =>
          refine ⟨.Err (fromR72Error e), ?_⟩
          rw [RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72, hr]
          rfl

/-- Every actual `sampler.circle_sample` call succeeds and returns a point on
    the retained R0P circle, without assuming success of its QM31 sampler or
    mapper calls. -/
theorem circle_sample_total_on_circle
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow) :
    ∃ p : circle.SecureCirclePoint,
      sampler.circle_sample block row = .ok p ∧
      RawCircleSampleActualPolicyV1.R0PCirclePoint p := by
  obtain ⟨q, hsample, hq⟩ := sampler_total_canonical block
  obtain ⟨r, hmapper⟩ := mapper_result_total q hq
  cases r with
  | Ok p =>
      have hout := RawCircleSampleEmittedWrapperLaw.success_returns_point
        block row q p hsample hmapper
      exact ⟨p, hout,
        RawCircleSampleActualPolicyV1.successfulCircleSampleOnR0PCircle
          block row q p hsample hq hout⟩
  | Err e =>
      cases row with
      | First =>
          have hout0 := RawCircleSampleActualFallbackResultV4.firstFallbackActual
            block q e hsample hmapper
          have hout : sampler.circle_sample block .First =
              .ok RawCircleSampleActualFallbackCircleV2.fallbackPoint0 := by
            simpa only [RawCircleSampleActualFallbackCircleV2.fallbackPoint0] using hout0
          exact ⟨RawCircleSampleActualFallbackCircleV2.fallbackPoint0, hout,
            RawCircleSampleActualPolicyV1.successfulCircleSampleOnR0PCircle
              block .First q RawCircleSampleActualFallbackCircleV2.fallbackPoint0
              hsample hq hout⟩
      | Second =>
          have hout0 := RawCircleSampleActualFallbackResultV4.secondFallbackActual
            block q e hsample hmapper
          have hout : sampler.circle_sample block .Second =
              .ok RawCircleSampleActualFallbackCircleV2.fallbackPoint1 := by
            simpa only [RawCircleSampleActualFallbackCircleV2.fallbackPoint1] using hout0
          exact ⟨RawCircleSampleActualFallbackCircleV2.fallbackPoint1, hout,
            RawCircleSampleActualPolicyV1.successfulCircleSampleOnR0PCircle
              block .Second q RawCircleSampleActualFallbackCircleV2.fallbackPoint1
              hsample hq hout⟩

#print axioms sampler_total_canonical
#print axioms mapper_result_total
#print axioms circle_sample_total_on_circle
end RawCircleSampleActualPolicyUnconditionalV1
end AspisR1CircleSampleWrapper
