import R1Z.PV_RunJoin_CircleR72Op1552
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op16 (self : CM) :
    AspisR72Sampler.field.CM31.inv (encCM self) = (do let x ← PV_RunJoin_CircleR72Raw52.field.CM31.inv self; ok (encCM x)) := by
  unfold AspisR72Sampler.field.CM31.inv PV_RunJoin_CircleR72Raw52.field.CM31.inv
  have hi : AspisR72Sampler.field.M31.inv = PV_RunJoin_CircleR72Raw52.field.M31.inv := funext op15
  rw [hi]
  exact op11 self PV_RunJoin_CircleR72Raw52.field.M31.inv

#print axioms op16
end R1Z.PV_RunJoin_CircleR72Ops52
