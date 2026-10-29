import R1Z.PV_RunJoin_CircleR72Op2852
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op29 (a : U32) (b : U32) :
    AspisR72Sampler.field.CM31.new a b = (do let x ← PV_RunJoin_CircleR72Raw52.field.CM31.new a b; ok (encCM x)) := by
  unfold AspisR72Sampler.field.CM31.new PV_RunJoin_CircleR72Raw52.field.CM31.new
  simp only [cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals first | rfl | simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op29
end R1Z.PV_RunJoin_CircleR72Ops52
