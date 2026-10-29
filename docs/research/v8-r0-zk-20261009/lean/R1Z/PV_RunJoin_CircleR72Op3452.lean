import R1Z.PV_RunJoin_CircleR72Op3352
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op34  :
    AspisR72Sampler.field.QM31.ONE  = encQ (PV_RunJoin_CircleR72Raw52.field.QM31.ONE ) := by
  unfold AspisR72Sampler.field.QM31.ONE PV_RunJoin_CircleR72Raw52.field.QM31.ONE
  all_goals simp only [encCM,encQ,encPoint,encOutcome,encError]
  all_goals rfl

#print axioms op34
end R1Z.PV_RunJoin_CircleR72Ops52
