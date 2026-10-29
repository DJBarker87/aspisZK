import R1Z.PV_RunJoin_CircleMapPrograms54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleMapSource54
abbrev Q := (U32 × U32) × (U32 × U32)

theorem complete (a : Q) :
    PV_RunJoin_CircleR72Raw52.circle.secure_ood_circle_point_from_parameter a=
      PV_RunJoin_CircleMapPrograms54.run a := by
  unfold PV_RunJoin_CircleR72Raw52.circle.secure_ood_circle_point_from_parameter
    PV_RunJoin_CircleR72Raw52.circle.secure_circle_point_from_parameter PV_RunJoin_CircleMapPrograms54.run
  simp only [bind_assoc_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro square _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro denominator _
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro inverse _
  cases inverse with
  | none => rfl
  | some inv =>
    simp only [PV_RunJoin_CircleR72Raw52.core.option.Option.ok_or,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro numerator _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro x _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro doubled _
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro y _
    rfl
#print axioms complete
end R1Z.PV_RunJoin_CircleMapSource54
