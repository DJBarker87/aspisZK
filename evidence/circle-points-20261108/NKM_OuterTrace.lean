import NKM_Trace
set_option autoImplicit false
noncomputable section
namespace NKM_OuterTrace
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase AspisV8R19
open NKM_circle NKM_FieldLaws NKM_CircleModel

def oodRun (t : NKM_circle.field.QM31) : Result (NKM_Roots.Reply × List NKM_Trace.Event × Bool) := do
 let (r,trace) ← NKM_Trace.run t
 match r with
 | .Err e => ok (.Err e,trace,false)
 | .Ok p =>
  let b ← NKM_circle.field.CM31.Insts.CoreCmpPartialEqCM31.eq t.c1 NKM_circle.field.CM31.ZERO
  ok ((if b then .Err .ParameterInCm31Subfield else .Ok p),trace,true)

theorem complete (t : QM31Exact) : oodRun (encode t)=
 ok (oodResult t,NKM_Trace.events t,decide (1+t*t≠0)) := by
 by_cases hd:1+t*t=0
 · simp only [oodRun,NKM_Trace.complete,circleResult,oodResult,hd,if_true,bind_tc_ok,not_true_eq_false,decide_false]
 · by_cases ht:t.im=0 <;>
    simp only [oodRun,NKM_Trace.complete,circleResult,oodResult,hd,ht,if_false,if_true,bind_tc_ok,
     cm_zero_test,decide_true,decide_false,Bool.false_eq_true,not_false_eq_true,point]

theorem erased (t : QM31Exact) :
 (do let r ← oodRun (encode t);ok r.1)=NKM_circle.circle.secure_ood_circle_point_from_parameter (encode t) := by
 rw [complete,ood_total];rfl

/-- Singular error returns without even performing the subsequent c1 comparison. -/
theorem error_order (t : QM31Exact) (hd:1+t*t=0) :
 oodRun (encode t)=ok (.Err .SingularParameter,NKM_Trace.events t,false) := by
 rw [complete]
 simp only [oodResult,hd,if_true,not_true_eq_false,decide_false]

#print axioms complete
#print axioms erased
#print axioms error_order
end NKM_OuterTrace
end
