import R1Z.PV_RunJoin_CircleR72Op3152
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op32 (self : Q) (rhs : Q) :
    AspisR72Sampler.field.QM31.sub (encQ self) (encQ rhs) = (do let x ← PV_RunJoin_CircleR72Raw52.field.QM31.sub self rhs; ok (encQ x)) := by
  unfold AspisR72Sampler.field.QM31.sub PV_RunJoin_CircleR72Raw52.field.QM31.sub
  simp only [op22,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals first | rfl | simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op32
end R1Z.PV_RunJoin_CircleR72Ops52
