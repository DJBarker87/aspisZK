import R1Z.PV_RunJoin_CircleR72Op3052
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op31 (self : Q) (rhs : Q) :
    AspisR72Sampler.field.QM31.mul (encQ self) (encQ rhs) = (do let x ← PV_RunJoin_CircleR72Raw52.field.QM31.mul self rhs; ok (encQ x)) := by
  unfold AspisR72Sampler.field.QM31.mul PV_RunJoin_CircleR72Raw52.field.QM31.mul
  simp only [op7,op20,op22,op24,op30,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op31
end R1Z.PV_RunJoin_CircleR72Ops52
