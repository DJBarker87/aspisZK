import LPp_WrapperFuns
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleEmittedWrapperLaw

theorem sampler_qm31_sample_eq_public (block : Array Std.U8 32#usize) :
    sampler.qm31_sample block = (do
      let q ← AspisR1PublicPreparation.sampler.qm31_sample block
      ok (fromPublicQM q)) := rfl

theorem secure_circle_eq_r72 (q : field.QM31) :
    circle.secure_ood_circle_point_from_parameter q = (do
      let r ← AspisR72Sampler.circle.secure_ood_circle_point_from_parameter (toR72QM q)
      match r with
      | .Ok p => ok (.Ok (fromR72Point p))
      | .Err e => ok (.Err (fromR72Error e))) := rfl

theorem fallback_adapter_eq_extracted (i : Std.Usize) :
    transcript.circle_fallback_point i = (do
      let p ← AspisR1CircleFallback.transcript.circle_fallback_point i
      ok (fromFallbackPoint p)) := rfl

theorem success_returns_point
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow)
    (q : field.QM31) (point : circle.SecureCirclePoint)
    (hsample : sampler.qm31_sample block = ok q)
    (hcircle : circle.secure_ood_circle_point_from_parameter q = ok (.Ok point)) :
    sampler.circle_sample block row = ok point := by
  simp [sampler.circle_sample, hsample, hcircle,
    core.result.Result.unwrap_or_else]

theorem first_fallback_returns_actual
    (block : Array Std.U8 32#usize)
    (q : field.QM31) (err : circle.CirclePointError)
    (hsample : sampler.qm31_sample block = ok q)
    (hcircle : circle.secure_ood_circle_point_from_parameter q = ok (.Err err)) :
    sampler.circle_sample block .First = transcript.circle_fallback_point 0#usize := by
  simp [sampler.circle_sample, hsample, hcircle,
    core.result.Result.unwrap_or_else,
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once]

theorem second_fallback_returns_actual
    (block : Array Std.U8 32#usize)
    (q : field.QM31) (err : circle.CirclePointError)
    (hsample : sampler.qm31_sample block = ok q)
    (hcircle : circle.secure_ood_circle_point_from_parameter q = ok (.Err err)) :
    sampler.circle_sample block .Second = transcript.circle_fallback_point 1#usize := by
  simp [sampler.circle_sample, hsample, hcircle,
    core.result.Result.unwrap_or_else,
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once]

theorem sample_failure_is_propagated
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow)
    (e : Error) (hsample : sampler.qm31_sample block = .fail e) :
    sampler.circle_sample block row = .fail e := by
  simp [sampler.circle_sample, hsample]

theorem mapper_failure_is_propagated
    (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow)
    (q : field.QM31) (e : Error)
    (hsample : sampler.qm31_sample block = ok q)
    (hmapper : circle.secure_ood_circle_point_from_parameter q = .fail e) :
    sampler.circle_sample block row = .fail e := by
  simp [sampler.circle_sample, hsample, hmapper]

#print axioms sampler_qm31_sample_eq_public
#print axioms secure_circle_eq_r72
#print axioms fallback_adapter_eq_extracted
#print axioms success_returns_point
#print axioms first_fallback_returns_actual
#print axioms second_fallback_returns_actual
#print axioms sample_failure_is_propagated
#print axioms mapper_failure_is_propagated

end RawCircleSampleEmittedWrapperLaw
end AspisR1CircleSampleWrapper
