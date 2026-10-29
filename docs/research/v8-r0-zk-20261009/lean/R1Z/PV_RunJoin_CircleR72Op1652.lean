import R1Z.PV_RunJoin_CircleR72Op1552
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op16 (self : CM) :
    AspisR72Sampler.field.CM31.inv (encCM self) = (do let x ← PV_RunJoin_CircleR72Raw52.field.CM31.inv self; ok (encCM x)) := by
  unfold AspisR72Sampler.field.CM31.inv PV_RunJoin_CircleR72Raw52.field.CM31.inv
  simp only [op11,op15,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op16
end R1Z.PV_RunJoin_CircleR72Ops52
