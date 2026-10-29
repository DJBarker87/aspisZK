import R1Z.PV_RunJoin_CircleOwnedOp2152
import R1Z.PV_RunJoin_CircleRawMap52
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RunJoin_CircleOwnedMap52
open PV_RunJoin_CircleOwnedCarrier52 PV_RunJoin_CircleOwnedOps52
namespace O
abbrev map := PV_AL_CircleOwned.map_parameter
end O

def encError (e : Bool) : PV_AL_CircleOwned.aspis_core.circle.CirclePointError :=
  if e then .ParameterInCm31Subfield else .SingularParameter

def encOutcome (r : core.result.Result Point Bool) :
    core.result.Result OP PV_AL_CircleOwned.aspis_core.circle.CirclePointError :=
  match r with | .Ok p => .Ok (encPoint p) | .Err e => .Err (encError e)

attribute [local irreducible] encCM encQ encPoint

theorem complete (q : Q) :
    PV_AL_CircleOwned.map_parameter (encQ q) = (do
      let r ← PV_RunJoin_CircleRawMap52.map_parameter q
      ok (encOutcome r)) := by
  unfold PV_AL_CircleOwned.map_parameter PV_RunJoin_CircleRawMap52.map_parameter
  rw [op18]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro square _
  rw [op14,op15]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro denominator _
  rw [op21]
  simp only [bind_assoc_eq,bind_tc_ok]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro inverse _
  cases inverse with
  | none => rfl
  | some inv =>
    simp only [Option.map_some]
    rw [op14,op16]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro numerator _
    rw [op17]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro x _
    rw [op15]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro doubled _
    rw [op17]
    simp only [bind_assoc_eq,bind_tc_ok]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro y _
    rw [PV_RunJoin_CircleOwnedProjection52.q_c1,op1,op0]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro bad _
    cases bad <;> rfl

#print axioms encError
#print axioms encOutcome
#print axioms complete
end R1Z.PV_RunJoin_CircleOwnedMap52
