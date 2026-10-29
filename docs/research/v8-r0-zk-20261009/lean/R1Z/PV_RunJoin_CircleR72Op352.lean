import R1Z.PV_RunJoin_CircleR72Op252
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op3  :
    AspisR72Sampler.field.P  = PV_RunJoin_CircleR72Raw52.field.P  := by
  unfold AspisR72Sampler.field.P PV_RunJoin_CircleR72Raw52.field.P
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op3
end R1Z.PV_RunJoin_CircleR72Ops52
