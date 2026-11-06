import NKM_OuterTrace
set_option autoImplicit false
noncomputable section
namespace NKM_FallbackTrace
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19 R0P.SemSource
open NKM_circle NKM_FieldLaws NKM_CircleModel

def parameter (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) : QM31Exact :=
 match row with | .First => circleFallbackParameter0 | .Second => circleFallbackParameter1

def run (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
 Result (NKM_circle.circle.SecureCirclePoint × List NKM_Trace.Event × Bool) := do
 let (r,trace,_) ← NKM_OuterTrace.oodRun (encode (parameter row))
 match r with
 | .Ok p => ok (p,trace,false)
 | .Err _ => ok (⟨NKM_circle.field.QM31.ONE,NKM_circle.field.QM31.ZERO⟩,trace,true)

theorem complete (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
 run row=ok (point (parameter row),NKM_Trace.events (parameter row),false) := by
 cases row <;>
  simp [run,NKM_OuterTrace.complete,parameter,oodResult,
   NKM_FallbackCertificate.denominator0,NKM_FallbackCertificate.denominator1,
   circleFallbackParameter0_im,circleFallbackParameter1_im,if_false,bind_tc_ok]

theorem emitted (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
 (do let r ← run row;ok r.1)=NKM_circle.transcript.circle_fallback_point (NKM_FallbackModel.index row) := by
 cases row <;> simp only [complete,bind_tc_ok,parameter,NKM_FallbackModel.index,
  NKM_FallbackModel.fallback0,NKM_FallbackModel.fallback1]

/-- The explicit native Err arm exists, but is never reached at either caller parameter. -/
theorem error_arm_unreachable (row : AspisR1CircleSampleWrapper.r0_transcript.CircleRow) :
 (do let r ← run row;ok r.2.2)=ok false := by
 rw [complete];rfl

#print axioms complete
#print axioms emitted
#print axioms error_arm_unreachable
end NKM_FallbackTrace
end
