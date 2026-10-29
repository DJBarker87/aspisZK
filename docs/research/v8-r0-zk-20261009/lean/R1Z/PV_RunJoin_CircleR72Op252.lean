import R1Z.PV_RunJoin_CircleR72Op152
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op2 (self : Q) :
    AspisR72Sampler.field.QM31.is_zero (encQ self) = PV_RunJoin_CircleR72Raw52.field.QM31.is_zero self := by
  unfold AspisR72Sampler.field.QM31.is_zero PV_RunJoin_CircleR72Raw52.field.QM31.is_zero
  simp only [op1,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op2
end R1Z.PV_RunJoin_CircleR72Ops52
