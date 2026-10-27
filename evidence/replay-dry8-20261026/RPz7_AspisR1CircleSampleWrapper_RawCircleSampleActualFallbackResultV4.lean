import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleEmittedWrapperLaw
import AspisR1CircleFallback.RawCircleFallbackOutputBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualFallbackResultV4

open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureProductExecution (encode)
open R0P.SemSource

/-- The actual wrapper's first fallback result, expressed through the checked
    extracted fallback owner. -/
theorem firstFallbackActual
    (block : Array Std.U8 32#usize) (q : field.QM31)
    (err : circle.CirclePointError)
    (hsample : sampler.qm31_sample block = ok q)
    (hcircle : circle.secure_ood_circle_point_from_parameter q = ok (.Err err)) :
    sampler.circle_sample block .First =
      .ok (fromFallbackPoint (AspisR1CircleFallback.fromR72Point
        (encodePoint (point circleFallbackParameter0)))) := by
  rw [RawCircleSampleEmittedWrapperLaw.first_fallback_returns_actual
    block q err hsample hcircle]
  rw [RawCircleSampleEmittedWrapperLaw.fallback_adapter_eq_extracted]
  rw [AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_zero_output]
  simp only [bind_tc_ok]

/-- The actual wrapper's second fallback result, expressed through the checked
    extracted fallback owner. -/
theorem secondFallbackActual
    (block : Array Std.U8 32#usize) (q : field.QM31)
    (err : circle.CirclePointError)
    (hsample : sampler.qm31_sample block = ok q)
    (hcircle : circle.secure_ood_circle_point_from_parameter q = ok (.Err err)) :
    sampler.circle_sample block .Second =
      .ok (fromFallbackPoint (AspisR1CircleFallback.fromR72Point
        (encodePoint (point circleFallbackParameter1)))) := by
  rw [RawCircleSampleEmittedWrapperLaw.second_fallback_returns_actual
    block q err hsample hcircle]
  rw [RawCircleSampleEmittedWrapperLaw.fallback_adapter_eq_extracted]
  rw [AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_one_output]
  simp only [bind_tc_ok]

#print axioms firstFallbackActual
#print axioms secondFallbackActual

end RawCircleSampleActualFallbackResultV4
end AspisR1CircleSampleWrapper
