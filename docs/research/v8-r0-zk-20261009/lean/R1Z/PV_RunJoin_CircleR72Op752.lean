import R1Z.PV_RunJoin_CircleR72Op652
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op7 (x : CM) :
    AspisR72Sampler.field.mul_by_r (encCM x) = (do let x ← PV_RunJoin_CircleR72Raw52.field.mul_by_r x; ok (encCM x)) := by
  unfold AspisR72Sampler.field.mul_by_r PV_RunJoin_CircleR72Raw52.field.mul_by_r
  simp only [op4,op5,op6,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op7
end R1Z.PV_RunJoin_CircleR72Ops52
