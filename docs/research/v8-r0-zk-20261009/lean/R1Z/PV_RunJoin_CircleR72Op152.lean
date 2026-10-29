import R1Z.PV_RunJoin_CircleR72Op052
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op1 (self : CM) :
    AspisR72Sampler.field.CM31.is_zero (encCM self) = PV_RunJoin_CircleR72Raw52.field.CM31.is_zero self := by
  unfold AspisR72Sampler.field.CM31.is_zero PV_RunJoin_CircleR72Raw52.field.CM31.is_zero
  simp only [op0,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op1
end R1Z.PV_RunJoin_CircleR72Ops52
