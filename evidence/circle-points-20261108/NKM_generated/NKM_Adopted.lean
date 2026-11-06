import NKM_Domains
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleEmittedWrapperLaw
import AspisR1CircleFallback.RawCircleFallbackOutputBridge
set_option autoImplicit false
noncomputable section
namespace NKM_Adopted
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19
open NKM_FieldLaws NKM_CircleModel

def toWrapper (x : NKM_circle.field.QM31) : AspisR1CircleSampleWrapper.field.QM31 :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def wrapperPoint (p : NKM_circle.circle.SecureCirclePoint) : AspisR1CircleSampleWrapper.circle.SecureCirclePoint :=
 ⟨toWrapper p.x,toWrapper p.y⟩
def wrapperError : NKM_circle.circle.CirclePointError → AspisR1CircleSampleWrapper.circle.CirclePointError
 | .SingularParameter => .SingularParameter
 | .ParameterInCm31Subfield => .ParameterInCm31Subfield
def wrapperResult (r : NKM_Roots.Reply) : core.result.Result AspisR1CircleSampleWrapper.circle.SecureCirclePoint AspisR1CircleSampleWrapper.circle.CirclePointError :=
 match r with | .Ok p => .Ok (wrapperPoint p) | .Err e => .Err (wrapperError e)

theorem ood (t : QM31Exact) :
 (do let r ← NKM_circle.circle.secure_ood_circle_point_from_parameter (encode t);ok (wrapperResult r)) =
 _root_.circle.secure_ood_circle_point_from_parameter (toWrapper (encode t)) := by
 rw [NKM_CircleModel.ood_source,AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72]
 simp only [bind_assoc_eq,bind_tc_ok]
 have h : _root_.toR72QM (toWrapper (encode t))=SamplerClosureProductExecution.encode t := by
  change NKM_circle.toQ (NKM_circle.fromQ (SamplerClosureProductExecution.encode t)) = _
  exact NKM_circle.to_from _
 rw [h]
 congr 1
 funext r
 cases r with
 | Ok p => rfl
 | Err e => cases e <;> rfl

def toFallback (x : NKM_circle.field.QM31) : AspisR1CircleFallback.field.QM31 :=
 ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fallbackPoint (p : NKM_circle.circle.SecureCirclePoint) : AspisR1CircleFallback.circle.SecureCirclePoint :=
 ⟨toFallback p.x,toFallback p.y⟩

theorem fallback0 :
 (do let p ← NKM_circle.transcript.circle_fallback_point 0#usize;ok (fallbackPoint p)) =
 AspisR1CircleFallback.transcript.circle_fallback_point 0#usize := by
 rw [NKM_FallbackModel.fallback0,AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_zero_output]
 rw [point_cohort]
 rfl

theorem fallback1 :
 (do let p ← NKM_circle.transcript.circle_fallback_point 1#usize;ok (fallbackPoint p)) =
 AspisR1CircleFallback.transcript.circle_fallback_point 1#usize := by
 rw [NKM_FallbackModel.fallback1,AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_one_output]
 rw [point_cohort]
 rfl

theorem fallback (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
 (do let p ← NKM_circle.transcript.circle_fallback_point (NKM_FallbackModel.index row);ok (fallbackPoint p)) =
 AspisR1CircleFallback.transcript.circle_fallback_point (NKM_FallbackModel.index row) := by
 cases row
 · exact fallback0
 · exact fallback1

#print ood
#print fallback
#print axioms ood
#print axioms fallback0
#print axioms fallback1
#print axioms fallback
end NKM_Adopted
end
