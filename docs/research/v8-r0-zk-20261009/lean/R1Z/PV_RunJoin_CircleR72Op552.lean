import R1Z.PV_RunJoin_CircleR72Op452
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op5 (self : U32) :
    AspisR72Sampler.field.M31.double self = PV_RunJoin_CircleR72Raw52.field.M31.double self := by
  unfold AspisR72Sampler.field.M31.double PV_RunJoin_CircleR72Raw52.field.M31.double
  simp only [op4,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op5
end R1Z.PV_RunJoin_CircleR72Ops52
