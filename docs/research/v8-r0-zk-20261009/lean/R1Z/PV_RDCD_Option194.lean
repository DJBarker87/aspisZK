import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD_Option194
open Aeneas Aeneas.Std Result
abbrev CF (T : Type) := core.ops.control_flow.ControlFlow (Option core.convert.Infallible) T
/-- Direct match in core/src/option.rs, deployed1.94.1 Try::branch. -/
def branch {T : Type} (self : Option T) : Result (CF T) :=
  match self with
  | some v => ok (.Continue v)
  | none => ok (.Break none)
/-- The residual match has only None; Infallible has no constructors. -/
def fromResidual (T : Type) (residual : Option core.convert.Infallible) : Result (Option T) :=
  match residual with
  | none => ok none
  | some impossible => nomatch impossible

theorem branch_some {T : Type} (v : T) : branch (some v) = ok (.Continue v) := rfl
theorem branch_none (T : Type) : branch (none : Option T) = ok (.Break none) := rfl
theorem residual_complete (T : Type) (o : Option core.convert.Infallible) :
    fromResidual T o = ok none := by
  cases o with
  | none => rfl
  | some impossible => exact nomatch impossible
/-- Complete error-preserving semantics of ? on Option, including a failing continuation. -/
theorem question_mark {T U : Type} (o : Option T) (next : T → Result (Option U)) :
    (do
      let cf ← branch o
      match cf with
      | .Continue v => next v
      | .Break r => fromResidual U r) =
    (match o with | none => ok none | some v => next v) := by
  cases o <;> rfl
#print axioms branch_some
#print axioms branch_none
#print axioms residual_complete
#print axioms question_mark
end R1Z.PV_RDCD_Option194
