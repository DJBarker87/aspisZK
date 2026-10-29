import R1Z.PV_RunJoin_CircleR72Op1352
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op14 (value : U32) (count : Std.Usize) :
    AspisR72Sampler.field.square_n value count = PV_RunJoin_CircleR72Raw52.field.square_n value count := by
  unfold AspisR72Sampler.field.square_n PV_RunJoin_CircleR72Raw52.field.square_n
  simp only [op13,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op14
end R1Z.PV_RunJoin_CircleR72Ops52
