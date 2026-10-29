import R1Z.PV_RunJoin_CircleR72Op3452
import R1Z.PV_RunJoin_CircleR72Raw52
import AspisR72Sampler.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Ops52
open PV_RunJoin_CircleR72Carrier52
attribute [local irreducible] encCM encQ
theorem op35 (parameter1 : Q) :
    AspisR72Sampler.circle.secure_circle_point_from_parameter (encQ parameter1) = (do let x ← PV_RunJoin_CircleR72Raw52.circle.secure_circle_point_from_parameter parameter1; ok (encOutcome x)) := by
  unfold AspisR72Sampler.circle.secure_circle_point_from_parameter
    PV_RunJoin_CircleR72Raw52.circle.secure_circle_point_from_parameter
  rw [op26]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro square _
  rw [op34,op33]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro denominator _
  rw [op23]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro inverse _
  cases inverse with
  | none => rfl
  | some inv =>
    simp only [Option.map_some,AspisR72Sampler.core.option.Option.ok_or,
      PV_RunJoin_CircleR72Raw52.core.option.Option.ok_or,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    rw [op32]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro numerator _
    rw [op31]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro x _
    rw [op33]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro doubled _
    rw [op31]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro y _
    rfl

#print axioms op35
end R1Z.PV_RunJoin_CircleR72Ops52
