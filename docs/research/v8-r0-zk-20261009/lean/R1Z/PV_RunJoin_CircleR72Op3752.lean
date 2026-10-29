import R1Z.PV_RunJoin_CircleR72Op3652
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op37 (self : U32) (other : U32) :
    AspisR72Sampler.field.M31.Insts.CoreCmpPartialEqM31.eq self other = PV_RunJoin_CircleR72Raw52.field.M31.Insts.CoreCmpPartialEqM31.eq self other := by
  unfold AspisR72Sampler.field.M31.Insts.CoreCmpPartialEqM31.eq PV_RunJoin_CircleR72Raw52.field.M31.Insts.CoreCmpPartialEqM31.eq
  simp only [cm_a,cm_b,q_c0,q_c1,bind_assoc_eq,bind_tc_ok]
  all_goals rfl

#print axioms op37
end R1Z.PV_RunJoin_CircleR72Ops52
