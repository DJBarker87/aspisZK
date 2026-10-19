import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1
import AspisR1CircleFallback.RawCircleFallbackOutputBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualFallbackCircleV2

open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureProductExecution (encode)
open R0P.SemSource

def fallbackPoint0 : circle.SecureCirclePoint :=
  fromFallbackPoint (AspisR1CircleFallback.fromR72Point
    (encodePoint (point circleFallbackParameter0)))

def fallbackPoint1 : circle.SecureCirclePoint :=
  fromFallbackPoint (AspisR1CircleFallback.fromR72Point
    (encodePoint (point circleFallbackParameter1)))

theorem firstFallbackPointOnCircle :
    (algebraMap QM31Exact AspisWideTower.WideExact
      (decode (toR72QM fallbackPoint0.x))) ^ 2 +
    (algebraMap QM31Exact AspisWideTower.WideExact
      (decode (toR72QM fallbackPoint0.y))) ^ 2 = 1 := by
  have hcoord := RawCircleSampleActualFallbackCoordinatesV1.firstFallbackCoordinates
  have hsum := congrArg (fun z : AspisWideTower.WideExact × AspisWideTower.WideExact =>
    z.1 ^ 2 + z.2 ^ 2) hcoord
  calc
    _ = circleFallback0.1.1 ^ 2 + circleFallback0.1.2 ^ 2 := hsum
    _ = 1 := circleFallback0.2

theorem secondFallbackPointOnCircle :
    (algebraMap QM31Exact AspisWideTower.WideExact
      (decode (toR72QM fallbackPoint1.x))) ^ 2 +
    (algebraMap QM31Exact AspisWideTower.WideExact
      (decode (toR72QM fallbackPoint1.y))) ^ 2 = 1 := by
  have hcoord := RawCircleSampleActualFallbackCoordinatesV1.secondFallbackCoordinates
  have hsum := congrArg (fun z : AspisWideTower.WideExact × AspisWideTower.WideExact =>
    z.1 ^ 2 + z.2 ^ 2) hcoord
  calc
    _ = circleFallback1.1.1 ^ 2 + circleFallback1.1.2 ^ 2 := hsum
    _ = 1 := circleFallback1.2

#print axioms firstFallbackPointOnCircle
#print axioms secondFallbackPointOnCircle

end RawCircleSampleActualFallbackCircleV2
end AspisR1CircleSampleWrapper
