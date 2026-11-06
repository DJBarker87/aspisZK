import NKM_FieldLaws
set_option autoImplicit false
noncomputable section
namespace NKM_CircleModel
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19
open NKM_circle NKM_FieldLaws

def point (t : QM31Exact) : circle.SecureCirclePoint :=
 ⟨encode ((1-t*t)*(1+t*t)⁻¹),encode ((t+t)*(1+t*t)⁻¹)⟩

def circleResult (t : QM31Exact) : core.result.Result circle.SecureCirclePoint circle.CirclePointError :=
 if 1+t*t=0 then .Err .SingularParameter else .Ok (point t)

def oodResult (t : QM31Exact) : core.result.Result circle.SecureCirclePoint circle.CirclePointError :=
 if 1+t*t=0 then .Err .SingularParameter
 else if t.im=0 then .Err .ParameterInCm31Subfield else .Ok (point t)

theorem singular (t : QM31Exact) (hd : 1+t*t=0) :
 circle.secure_circle_point_from_parameter (encode t)=ok (.Err .SingularParameter) := by
 simp only [circle.secure_circle_point_from_parameter,square,one,add,hd,inverse_zero,bind_tc_ok,core.option.Option.ok_or]
 rfl

theorem regular (t : QM31Exact) (hd : 1+t*t≠0) :
 circle.secure_circle_point_from_parameter (encode t)=ok (.Ok (point t)) := by
 simp only [circle.secure_circle_point_from_parameter,square,one,add,inverse_nonzero _ hd,bind_tc_ok,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
 simp only [bind_tc_ok,sub,mul,add,point]

theorem circle_total (t : QM31Exact) :
 circle.secure_circle_point_from_parameter (encode t)=ok (circleResult t) := by
 by_cases hd : 1+t*t=0
 · rw [singular t hd];simp only [circleResult,hd,if_true]
 · rw [regular t hd];simp only [circleResult,hd,if_false]

theorem cm_zero_test (t : QM31Exact) :
 field.CM31.Insts.CoreCmpPartialEqCM31.eq (encode t).c1 field.CM31.ZERO = ok (decide (t.im=0)) := by
 have h := SamplerClosureCircleSourceExecution.cm_eq_zero t.im
 simpa only [field.CM31.Insts.CoreCmpPartialEqCM31.eq,field.M31.Insts.CoreCmpPartialEqM31.eq,
  AspisR72Sampler.field.CM31.Insts.CoreCmpPartialEqCM31.eq,AspisR72Sampler.field.M31.Insts.CoreCmpPartialEqM31.eq,
  field.CM31.ZERO,AspisR72Sampler.field.CM31.ZERO,encode,fromQ,fromCM,SamplerClosureProductExecution.encode,encodeCM,bind_tc_ok] using h

theorem ood_total (t : QM31Exact) :
 circle.secure_ood_circle_point_from_parameter (encode t)=ok (oodResult t) := by
 by_cases hd : 1+t*t=0
 · simp only [circle.secure_ood_circle_point_from_parameter,singular t hd,bind_tc_ok,oodResult,hd,if_true]
   rfl
 · by_cases ht : t.im=0
   · simp only [circle.secure_ood_circle_point_from_parameter,regular t hd,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,cm_zero_test,ht,decide_true,if_true,oodResult,hd,if_false]
   · simp only [circle.secure_ood_circle_point_from_parameter,regular t hd,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,cm_zero_test,ht,decide_false,if_false,Bool.false_eq_true,oodResult,hd]

def fromPoint (p : AspisR72Sampler.circle.SecureCirclePoint) : circle.SecureCirclePoint := ⟨fromQ p.x,fromQ p.y⟩
def fromError : AspisR72Sampler.circle.CirclePointError → circle.CirclePointError
 | .SingularParameter => .SingularParameter
 | .ParameterInCm31Subfield => .ParameterInCm31Subfield
def fromResult (r : core.result.Result AspisR72Sampler.circle.SecureCirclePoint AspisR72Sampler.circle.CirclePointError) :
 core.result.Result circle.SecureCirclePoint circle.CirclePointError :=
 match r with | .Ok p => .Ok (fromPoint p) | .Err e => .Err (fromError e)

theorem point_cohort (t : QM31Exact) :
 point t = fromPoint (SamplerClosureCircleSourceExecution.encodePoint (SamplerCirclePolicy.point t)) := by
 simp only [point,fromPoint,SamplerClosureCircleSourceExecution.encodePoint,SamplerCirclePolicy.point,
  AspisV8R15.CircleChord.px,AspisV8R15.CircleChord.py,pow_two,div_eq_mul_inv,two_mul,encode]

theorem circle_source (t : QM31Exact) :
 circle.secure_circle_point_from_parameter (encode t) =
 (do let r ← AspisR72Sampler.circle.secure_circle_point_from_parameter (SamplerClosureProductExecution.encode t)
     ok (fromResult r)) := by
 by_cases hd : 1+t*t=0
 · rw [singular t hd,SamplerClosureCircleSourceExecution.circle_singular t hd];rfl
 · rw [regular t hd,SamplerClosureCircleSourceExecution.circle_regular t hd]
   simp only [bind_tc_ok,fromResult,point_cohort]

theorem ood_source (t : QM31Exact) :
 circle.secure_ood_circle_point_from_parameter (encode t) =
 (do let r ← AspisR72Sampler.circle.secure_ood_circle_point_from_parameter (SamplerClosureProductExecution.encode t)
     ok (fromResult r)) := by
 rw [ood_total,SamplerClosureCircleSourceExecution.encoded_execution]
 by_cases hd : 1+t*t=0
 · simp only [oodResult,hd,if_true,SamplerCirclePolicy.pureMap,pow_two,bind_tc_ok,
    SamplerClosureCircleSourceExecution.encodeResult,SamplerClosureCircleSourceExecution.encodeError,fromResult,fromError]
 · by_cases ht : t.im=0 <;>
    simp only [oodResult,hd,ht,if_true,if_false,SamplerCirclePolicy.pureMap,pow_two,bind_tc_ok,
     SamplerClosureCircleSourceExecution.encodeResult,SamplerClosureCircleSourceExecution.encodeError,fromResult,fromError,point_cohort]

#print axioms singular
#print axioms regular
#print axioms circle_total
#print axioms cm_zero_test
#print axioms ood_total
#print axioms point_cohort
#print axioms circle_source
#print axioms ood_source
end NKM_CircleModel
end
