import AspisR1CircleSampleWrapper.RawCircleSampleActualSecureBridgeV1
import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCircleV2
import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackResultV4

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualPolicyV1

open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureProductExecution (encode)
open R0P.SemSource

def R0PCirclePoint (p : circle.SecureCirclePoint) : Prop :=
  (algebraMap QM31Exact AspisWideTower.WideExact
    (decode (toR72QM p.x))) ^ 2 +
  (algebraMap QM31Exact AspisWideTower.WideExact
    (decode (toR72QM p.y))) ^ 2 = 1

/-- A successful secure mapper result from the actual wrapper is a point on
    the retained R0P circle, provided its sampled parameter satisfies the
    existing R72 canonical-input contract. -/
theorem secureMapperOutputOnR0PCircle
    (q : field.QM31) (p : circle.SecureCirclePoint)
    (hq : AspisV8R19.SamplerClosureProductCorrectness.Canonical (toR72QM q))
    (hp : circle.secure_ood_circle_point_from_parameter q = .ok (.Ok p)) :
    R0PCirclePoint p := by
  obtain ⟨p72, _, hpoint, _, _, _, _, hcircle⟩ :=
    RawCircleSampleActualSecureBridgeV1.wrapper_secure_success_circle_facts q hq p hp
  subst p
  have hmap : algebraMap QM31Exact AspisWideTower.WideExact
      ((decode p72.x)^2 + (decode p72.y)^2) = 1 := by
    simpa using congrArg
      (algebraMap QM31Exact AspisWideTower.WideExact) hcircle
  change (algebraMap QM31Exact AspisWideTower.WideExact (decode p72.x))^2 +
    (algebraMap QM31Exact AspisWideTower.WideExact (decode p72.y))^2 = 1
  simpa only [map_add, map_pow, map_one] using hmap

/-- The actual emitted sampler wrapper returns a point on the retained R0P
    circle whenever its mapper succeeds. This theorem covers the secure and
    error-fallback arms; sampler and mapper failures remain failures. -/
theorem successfulCircleSampleOnR0PCircle
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow)
    (q : field.QM31) (p : circle.SecureCirclePoint)
    (hsample : sampler.qm31_sample block = ok q)
    (hq : AspisV8R19.SamplerClosureProductCorrectness.Canonical (toR72QM q))
    (hout : sampler.circle_sample block row = .ok p) :
    R0PCirclePoint p := by
  cases hr : circle.secure_ood_circle_point_from_parameter q with
  | fail e =>
      simp [sampler.circle_sample, hsample, hr] at hout
  | div =>
      simp [sampler.circle_sample, hsample, hr] at hout
  | ok result =>
      cases result with
      | Ok securePoint =>
          have hrun := RawCircleSampleEmittedWrapperLaw.success_returns_point
            block row q securePoint hsample hr
          have hp : securePoint = p := Result.ok.inj (hrun.symm.trans hout)
          subst p
          exact secureMapperOutputOnR0PCircle q securePoint hq hr
      | Err err =>
          cases row with
          | First =>
              have hrun0 := RawCircleSampleActualFallbackResultV4.firstFallbackActual
                block q err hsample hr
              have hrun : sampler.circle_sample block .First =
                  .ok RawCircleSampleActualFallbackCircleV2.fallbackPoint0 := by
                simpa only [RawCircleSampleActualFallbackCircleV2.fallbackPoint0] using hrun0
              have hp := Result.ok.inj (hrun.symm.trans hout)
              rw [← hp]
              exact RawCircleSampleActualFallbackCircleV2.firstFallbackPointOnCircle
          | Second =>
              have hrun0 := RawCircleSampleActualFallbackResultV4.secondFallbackActual
                block q err hsample hr
              have hrun : sampler.circle_sample block .Second =
                  .ok RawCircleSampleActualFallbackCircleV2.fallbackPoint1 := by
                simpa only [RawCircleSampleActualFallbackCircleV2.fallbackPoint1] using hrun0
              have hp := Result.ok.inj (hrun.symm.trans hout)
              rw [← hp]
              exact RawCircleSampleActualFallbackCircleV2.secondFallbackPointOnCircle

#print axioms secureMapperOutputOnR0PCircle
#print axioms successfulCircleSampleOnR0PCircle

end RawCircleSampleActualPolicyV1
end AspisR1CircleSampleWrapper
