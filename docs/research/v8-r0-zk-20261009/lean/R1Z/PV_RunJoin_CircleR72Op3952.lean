import R1Z.PV_RunJoin_CircleR72Op3852
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op39 (parameter1 : Q) :
    AspisR72Sampler.circle.secure_ood_circle_point_from_parameter (encQ parameter1) = (do let x ← PV_RunJoin_CircleR72Raw52.circle.secure_ood_circle_point_from_parameter parameter1; ok (encOutcome x)) := by
  unfold AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
    PV_RunJoin_CircleR72Raw52.circle.secure_ood_circle_point_from_parameter
  rw [op35]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro r _
  cases r with
  | Err e => cases e <;> rfl
  | Ok point =>
    simp only [encOutcome,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    rw [q_c1,op36,op38]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro bad _
    cases bad <;> rfl

#print axioms op39
end R1Z.PV_RunJoin_CircleR72Ops52
