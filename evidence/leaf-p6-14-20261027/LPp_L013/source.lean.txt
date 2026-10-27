import LPp_WrapperFuns
import LPp_WrapperRawCircleSampleEmittedWrapperLaw
import LPp_WrapperRawCircleSampleActualSamplerCanonicalV1
import LPp_FallbackValues

set_option autoImplicit false
noncomputable section
namespace LPp.Closure
open Aeneas Aeneas.Std Result AspisR1CircleSampleWrapper
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureProductExecution (encode)
open AspisV8R19.SamplerCirclePolicy
open R0P.SemSource

def fallback (row : r0_transcript.CircleRow) : circle.SecureCirclePoint :=
  fromFallbackPoint (AspisR1CircleFallback.fromR72Point (encodePoint
    (match row with
    | .First => (LPp.Fallback.x0, LPp.Fallback.y0)
    | .Second => (LPp.Fallback.x1, LPp.Fallback.y1))))

def resolve (r : core.result.Result circle.SecureCirclePoint circle.CirclePointError)
    (row : r0_transcript.CircleRow) : circle.SecureCirclePoint :=
  match r with
  | .Ok p => p
  | .Err _ => fallback row

theorem capture (row : r0_transcript.CircleRow) (err : circle.CirclePointError) :
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once
      row err = .ok (fallback row) := by
  cases row <;>
    simp only [sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once,
      bind_tc_ok, transcript.circle_fallback_point, LPp.Fallback.fallback0,
      LPp.Fallback.fallback1, fallback]

theorem capture_ignores_error (row : r0_transcript.CircleRow)
    (e₁ e₂ : circle.CirclePointError) :
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once row e₁ =
    sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once row e₂ := by
  rw [capture, capture]

theorem native_step (block : Array Std.U8 32#usize) (row : r0_transcript.CircleRow)
    (q : field.QM31)
    (r : core.result.Result circle.SecureCirclePoint circle.CirclePointError)
    (sample : sampler.qm31_sample block = .ok q)
    (mapped : circle.secure_ood_circle_point_from_parameter q = .ok r) :
    sampler.circle_sample block row = .ok (resolve r row) := by
  simp only [sampler.circle_sample, sample, mapped, bind_tc_ok]
  cases r with
  | Ok p => rfl
  | Err e => exact capture row e

theorem sampler_domain (block : Array Std.U8 32#usize) :
    ∃ q : field.QM31, sampler.qm31_sample block = .ok q ∧ Canonical (toR72QM q) := by
  obtain ⟨q, hq, _, _⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total block
  have h : sampler.qm31_sample block = .ok (fromPublicQM q) := by
    rw [RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public, hq]
    rfl
  exact ⟨_, h, RawCircleSampleActualSamplerCanonicalV1.successful_sample_toR72_canonical block _ h⟩

#print axioms capture
#print axioms capture_ignores_error
#print axioms native_step
#print axioms sampler_domain
end LPp.Closure
