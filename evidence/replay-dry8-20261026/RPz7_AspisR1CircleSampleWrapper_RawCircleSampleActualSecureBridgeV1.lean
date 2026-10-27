import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleEmittedWrapperLaw
import AspisV8R19.SamplerClosureCircleSourceExecution

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualSecureBridgeV1

/-- A secure point returned by the actual emitted R1 circle mapper is the
    structural adapter of a successful point from the retained R72 mapper. -/
theorem wrapper_success_to_r72
    (q : field.QM31) (p : circle.SecureCirclePoint)
    (hp : circle.secure_ood_circle_point_from_parameter q = .ok (.Ok p)) :
    ∃ p72 : AspisR72Sampler.circle.SecureCirclePoint,
      AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
        (toR72QM q) = .ok (.Ok p72) ∧ fromR72Point p72 = p := by
  rw [RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72] at hp
  cases hr : AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
      (toR72QM q) with
  | fail err => simp [hr] at hp
  | div => simp [hr] at hp
  | ok out =>
    cases out with
    | Err e => simp [hr] at hp
    | Ok p72 =>
      simp only [hr, bind_tc_ok] at hp
      have hpoint : fromR72Point p72 = p := by
        simpa only [Result.ok.injEq, core.result.Result.Ok.injEq] using hp
      exact ⟨p72, rfl, hpoint⟩

/-- For a canonical sampled parameter, secure output from the actual emitted
    mapper retains the R72 mapped point and its circle equation. -/
theorem wrapper_secure_success_circle_facts
    (q : field.QM31)
    (hq : AspisV8R19.SamplerClosureProductCorrectness.Canonical (toR72QM q))
    (p : circle.SecureCirclePoint)
    (hp : circle.secure_ood_circle_point_from_parameter q = .ok (.Ok p)) :
    ∃ p72 : AspisR72Sampler.circle.SecureCirclePoint,
      AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
        (toR72QM q) = .ok (.Ok p72) ∧ fromR72Point p72 = p ∧
      (AspisV8R19.SamplerClosureProductCorrectness.decode (toR72QM q)).im ≠ 0 ∧
      AspisV8R19.SamplerClosureProductCorrectness.Canonical p72.x ∧
      AspisV8R19.SamplerClosureProductCorrectness.Canonical p72.y ∧
      AspisV8R19.SamplerClosureCircleSourceExecution.decodePoint p72 =
        AspisV8R19.SamplerCirclePolicy.point
          (AspisV8R19.SamplerClosureProductCorrectness.decode (toR72QM q)) ∧
      (AspisV8R19.SamplerClosureProductCorrectness.decode p72.x)^2 +
        (AspisV8R19.SamplerClosureProductCorrectness.decode p72.y)^2 = 1 := by
  obtain ⟨p72, hr, hpoint⟩ := wrapper_success_to_r72 q p hp
  obtain ⟨ht, hx, hy, hmap, hcircle⟩ :=
    AspisV8R19.SamplerClosureCircleSourceExecution.successful_output
      (toR72QM q) hq p72 hr
  exact ⟨p72, hr, hpoint, ht, hx, hy, hmap, hcircle⟩

#print axioms wrapper_success_to_r72
#print axioms wrapper_secure_success_circle_facts

end RawCircleSampleActualSecureBridgeV1
end AspisR1CircleSampleWrapper
