import R1Z.PV_RunJoin_CircleR72Op1752
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op18 (value : Std.U64) :
    AspisR72Sampler.field.M31.reduce_u64 value = PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 value := by
  unfold AspisR72Sampler.field.M31.reduce_u64 PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64
  simp only [op8,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals first | rfl | simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op18
end R1Z.PV_RunJoin_CircleR72Ops52
