import R1Z.PV_RunJoin_CircleR72Op3552
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op36  :
    AspisR72Sampler.field.CM31.ZERO  = encCM (PV_RunJoin_CircleR72Raw52.field.CM31.ZERO ) := by
  unfold AspisR72Sampler.field.CM31.ZERO PV_RunJoin_CircleR72Raw52.field.CM31.ZERO
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op36
end R1Z.PV_RunJoin_CircleR72Ops52
