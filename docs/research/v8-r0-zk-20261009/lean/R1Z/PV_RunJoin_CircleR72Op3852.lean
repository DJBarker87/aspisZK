import R1Z.PV_RunJoin_CircleR72Op3752
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op38 (self : CM) (other : CM) :
    AspisR72Sampler.field.CM31.Insts.CoreCmpPartialEqCM31.eq (encCM self) (encCM other) = PV_RunJoin_CircleR72Raw52.field.CM31.Insts.CoreCmpPartialEqCM31.eq self other := by
  unfold AspisR72Sampler.field.CM31.Insts.CoreCmpPartialEqCM31.eq PV_RunJoin_CircleR72Raw52.field.CM31.Insts.CoreCmpPartialEqCM31.eq
  simp only [op37,cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals first | rfl | simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op38
end R1Z.PV_RunJoin_CircleR72Ops52
