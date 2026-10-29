import R1Z.PV_RunJoin_CircleR72Op1852
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op19 (self : CM) :
    AspisR72Sampler.field.CM31.square (encCM self) = (do let x ← PV_RunJoin_CircleR72Raw52.field.CM31.square self; ok (encCM x)) := by
  unfold AspisR72Sampler.field.CM31.square PV_RunJoin_CircleR72Raw52.field.CM31.square
  simp only [op3,op5,op9,op17,op18,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op19
end R1Z.PV_RunJoin_CircleR72Ops52
