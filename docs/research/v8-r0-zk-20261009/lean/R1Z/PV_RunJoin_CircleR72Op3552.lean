import R1Z.PV_RunJoin_CircleR72Op3452
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op35 (parameter1 : Q) :
    AspisR72Sampler.circle.secure_circle_point_from_parameter (encQ parameter1) = (do let x ← PV_RunJoin_CircleR72Raw52.circle.secure_circle_point_from_parameter parameter1; ok (encOutcome x)) := by
  unfold AspisR72Sampler.circle.secure_circle_point_from_parameter PV_RunJoin_CircleR72Raw52.circle.secure_circle_point_from_parameter
  simp only [op23,op26,op31,op32,op33,op34,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op35
end R1Z.PV_RunJoin_CircleR72Ops52
