import AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1
import AspisR1CircleSampleWrapper.RawCircleSampleActualSecureBridgeV1
import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackResultV4

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.SAP_WrapperCanonical
open AspisR1CircleSampleWrapper
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy


/-- Keep the fallback point symbolic while cancelling its structural adapters;
closed fallback field constants are never reduced. -/
theorem fallback_adapter_coordinates_canonical
    (p : AspisR72Sampler.circle.SecureCirclePoint)
    (hc : Canonical p.x ∧ Canonical p.y) :
    Canonical (toR72QM (fromFallbackPoint (AspisR1CircleFallback.fromR72Point p)).x) ∧
    Canonical (toR72QM (fromFallbackPoint (AspisR1CircleFallback.fromR72Point p)).y) := by
  change Canonical p.x ∧ Canonical p.y
  exact hc

/-- Coordinate canonicality of the retained emitted wrapper and its existing
concrete Lean callee adapters. This does not assert current Rust callee refinement. -/
theorem successful_wrapper_circle_coordinates_canonical
    (block : Array U8 32#usize) (row : r0_transcript.CircleRow) (p : circle.SecureCirclePoint)
    (hout : sampler.circle_sample block row = .ok p) :
    Canonical (toR72QM p.x) ∧ Canonical (toR72QM p.y) := by
  obtain ⟨q,hsample,hq⟩ := RawCircleSampleActualPolicyUnconditionalV1.sampler_total_canonical block
  cases hm : circle.secure_ood_circle_point_from_parameter q with
  | fail e =>
    have he := RawCircleSampleEmittedWrapperLaw.mapper_failure_is_propagated block row q e hsample hm
    rw [he] at hout
    cases hout
  | div =>
    simp only [sampler.circle_sample,hsample,bind_tc_ok,hm,bind_tc_div] at hout
    cases hout
  | ok result =>
    cases result with
    | Ok out =>
      have he := RawCircleSampleEmittedWrapperLaw.success_returns_point block row q out hsample hm
      have hp : out = p := Result.ok.inj (he.symm.trans hout)
      rw [← hp]
      obtain ⟨p72,_,heq,_,hx,hy,_,_⟩ :=
        RawCircleSampleActualSecureBridgeV1.wrapper_secure_success_circle_facts q hq out hm
      rw [← heq]
      change Canonical p72.x ∧ Canonical p72.y
      exact ⟨hx,hy⟩
    | Err e =>
      cases row with
      | First =>
        have he := RawCircleSampleActualFallbackResultV4.firstFallbackActual block q e hsample hm
        have hp := Result.ok.inj (he.symm.trans hout)
        rw [← hp]
        exact fallback_adapter_coordinates_canonical
          (encodePoint (point R0P.SemSource.circleFallbackParameter0)) (point_canonical _)
      | Second =>
        have he := RawCircleSampleActualFallbackResultV4.secondFallbackActual block q e hsample hm
        have hp := Result.ok.inj (he.symm.trans hout)
        rw [← hp]
        exact fallback_adapter_coordinates_canonical
          (encodePoint (point R0P.SemSource.circleFallbackParameter1)) (point_canonical _)

#print axioms fallback_adapter_coordinates_canonical
#print axioms successful_wrapper_circle_coordinates_canonical
end AspisR1.SAP_WrapperCanonical
