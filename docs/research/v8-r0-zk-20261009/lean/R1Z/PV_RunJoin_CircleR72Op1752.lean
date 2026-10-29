import R1Z.PV_RunJoin_CircleR72Op1652
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op17 (left : Std.U64) (right : Std.U64) :
    AspisR72Sampler.field.r23_product_u32_bounded left right = PV_RunJoin_CircleR72Raw52.field.r23_product_u32_bounded left right := by
  unfold AspisR72Sampler.field.r23_product_u32_bounded PV_RunJoin_CircleR72Raw52.field.r23_product_u32_bounded
  simp only [cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op17
end R1Z.PV_RunJoin_CircleR72Ops52
