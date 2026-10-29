import R1Z.PV_RunJoin_CircleR72Op3952
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op40  :
    AspisR72Sampler.field.M31.ZERO  = PV_RunJoin_CircleR72Raw52.field.M31.ZERO  := by
  unfold AspisR72Sampler.field.M31.ZERO PV_RunJoin_CircleR72Raw52.field.M31.ZERO
  all_goals first | rfl | simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op40
end R1Z.PV_RunJoin_CircleR72Ops52
