import R1Z.PV_RunJoin_CircleR72Op3252
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op33 (self : Q) (rhs : Q) :
    AspisR72Sampler.field.QM31.add (encQ self) (encQ rhs) = (do let x ← PV_RunJoin_CircleR72Raw52.field.QM31.add self rhs; ok (encQ x)) := by
  unfold AspisR72Sampler.field.QM31.add PV_RunJoin_CircleR72Raw52.field.QM31.add
  simp only [op24,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals first | rfl | simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op33
end R1Z.PV_RunJoin_CircleR72Ops52
