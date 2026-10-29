import R1Z.PV_RunJoin_CircleR72Op752
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op8 (x : Std.U64) :
    AspisR72Sampler.field.reduce_u64 x = PV_RunJoin_CircleR72Raw52.field.reduce_u64 x := by
  unfold AspisR72Sampler.field.reduce_u64 PV_RunJoin_CircleR72Raw52.field.reduce_u64
  simp only [op3,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op8
end R1Z.PV_RunJoin_CircleR72Ops52
