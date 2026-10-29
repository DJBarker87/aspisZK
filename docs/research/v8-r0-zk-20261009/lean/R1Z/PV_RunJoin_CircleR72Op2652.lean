import R1Z.PV_RunJoin_CircleR72Op2552
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op26 (self : Q) :
    AspisR72Sampler.field.QM31.square (encQ self) = (do let x ← PV_RunJoin_CircleR72Raw52.field.QM31.square self; ok (encQ x)) := by
  unfold AspisR72Sampler.field.QM31.square PV_RunJoin_CircleR72Raw52.field.QM31.square
  simp only [op7,op19,op20,op24,op25,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op26
end R1Z.PV_RunJoin_CircleR72Ops52
