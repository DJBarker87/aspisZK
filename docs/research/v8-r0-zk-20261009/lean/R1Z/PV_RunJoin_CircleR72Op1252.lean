import R1Z.PV_RunJoin_CircleR72Op1152
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op12 (iter : core.ops.range.Range Std.Usize) (value : U32) :
    AspisR72Sampler.field.square_n_loop.body iter value = PV_RunJoin_CircleR72Raw52.field.square_n_loop.body iter value := by
  unfold AspisR72Sampler.field.square_n_loop.body PV_RunJoin_CircleR72Raw52.field.square_n_loop.body
  simp only [op9,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op12
end R1Z.PV_RunJoin_CircleR72Ops52
