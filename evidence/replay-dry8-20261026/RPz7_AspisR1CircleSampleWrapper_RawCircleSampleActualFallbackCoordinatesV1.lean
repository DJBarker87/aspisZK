import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackResultV4
import AspisR1CircleFallback.RawCircleFallbackOutputBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualFallbackCoordinatesV1

open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureProductExecution (encode)
open R0P.SemSource

/-- Coordinates of the first actual wrapper fallback are the retained R0P
    circle-fallback coordinates. -/
theorem firstFallbackCoordinates :
    (algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromFallbackPoint
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter0)))).x)),
      algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromFallbackPoint
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter0)))).y))) =
      circleFallback0.1 := by
  change
    (algebraMap QM31Exact AspisWideTower.WideExact
        (decode (AspisR1CircleFallback.toR72QM
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter0))).x)),
      algebraMap QM31Exact AspisWideTower.WideExact
        (decode (AspisR1CircleFallback.toR72QM
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter0))).y))) =
      circleFallback0.1
  exact AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_zero_coordinates_match

/-- Coordinates of the second actual wrapper fallback are the retained R0P
    circle-fallback coordinates. -/
theorem secondFallbackCoordinates :
    (algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromFallbackPoint
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter1)))).x)),
      algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromFallbackPoint
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter1)))).y))) =
      circleFallback1.1 := by
  change
    (algebraMap QM31Exact AspisWideTower.WideExact
        (decode (AspisR1CircleFallback.toR72QM
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter1))).x)),
      algebraMap QM31Exact AspisWideTower.WideExact
        (decode (AspisR1CircleFallback.toR72QM
          (AspisR1CircleFallback.fromR72Point
            (encodePoint (point circleFallbackParameter1))).y))) =
      circleFallback1.1
  exact AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_one_coordinates_match

#print axioms firstFallbackCoordinates
#print axioms secondFallbackCoordinates

end RawCircleSampleActualFallbackCoordinatesV1
end AspisR1CircleSampleWrapper
