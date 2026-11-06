import NIX_CircleLogLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_SecureOodLaw
open Aeneas Aeneas.Std Result AspisR72Sampler
open NIX_CircleLogLaw (Q Point Err)

def oodReply (q : Q) (r : core.result.Result Point Err) : core.result.Result Point Err :=
 match r with
 | .Err e=>.Err e
 | .Ok p=>if q.c1.a=0#u32 ∧ q.c1.b=0#u32 then .Err .ParameterInCm31Subfield else .Ok p

/-- Raw-word equality, with no canonicality or nonzero-parameter restriction. -/
theorem zero_test (q : field.CM31) :
 field.CM31.Insts.CoreCmpPartialEqCM31.eq q field.CM31.ZERO=
 ok (decide (q.a=0#u32 ∧ q.b=0#u32)) := by
 rcases q with ⟨a,b⟩
 simp only [field.CM31.Insts.CoreCmpPartialEqCM31.eq,
  field.M31.Insts.CoreCmpPartialEqM31.eq,field.CM31.ZERO,bind_tc_ok]
 by_cases ha : a=0#u32 <;> by_cases hb : b=0#u32 <;> simp [ha,hb]

/-- Full error propagation precedes the subfield test, exactly as in the
native ood_dispatch log certificate; no enclosing success premise. -/
theorem source_of_log (q : Q) (r : core.result.Result Point Err)
 (callee : AspisR72Sampler.circle.secure_circle_point_from_parameter q=ok r) :
 AspisR72Sampler.circle.secure_ood_circle_point_from_parameter q=ok (oodReply q r) := by
 cases r with
 | Err e=>
   simp only [AspisR72Sampler.circle.secure_ood_circle_point_from_parameter,callee,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,oodReply]
   rfl
 | Ok p=>
   simp only [AspisR72Sampler.circle.secure_ood_circle_point_from_parameter,callee,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,zero_test,oodReply]
   by_cases zero : q.c1.a=0#u32 ∧ q.c1.b=0#u32 <;> simp [zero]

/-- Existing complete R72 source execution, transported through the SAME
structural adapter used by the adopted circle wrapper. -/
def wrapperReply (r : core.result.Result Point Err) :
 core.result.Result AspisR1CircleSampleWrapper.circle.SecureCirclePoint AspisR1CircleSampleWrapper.circle.CirclePointError :=
 match r with
 | .Ok p=>.Ok (AspisR1CircleSampleWrapper.fromR72Point p)
 | .Err e=>.Err (AspisR1CircleSampleWrapper.fromR72Error e)

theorem wrapper_source (q : AspisR1CircleSampleWrapper.field.QM31)
 (domain : AspisV8R19.SamplerClosureProductCorrectness.Canonical (AspisR1CircleSampleWrapper.toR72QM q)) :
 _root_.circle.secure_ood_circle_point_from_parameter q=
 ok (wrapperReply (AspisV8R19.SamplerClosureCircleSourceExecution.encodeResult
  (AspisV8R19.SamplerCirclePolicy.pureMap
   (AspisV8R19.SamplerClosureProductCorrectness.decode (AspisR1CircleSampleWrapper.toR72QM q))))) := by
 rw [AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72,
  AspisV8R19.SamplerClosureCircleSourceExecution.source_execution _ domain,bind_tc_ok]
 cases AspisV8R19.SamplerCirclePolicy.pureMap
  (AspisV8R19.SamplerClosureProductCorrectness.decode (AspisR1CircleSampleWrapper.toR72QM q)) <;> rfl

#print axioms zero_test
#print axioms source_of_log
#print axioms wrapper_source
end AspisR1.NIX_SecureOodLaw
end
