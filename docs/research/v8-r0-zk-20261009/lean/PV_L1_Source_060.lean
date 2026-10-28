import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_060
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (column : Slice aspis_core.field.M31) :
  Logged (core.result.Result Unit r1_wire.Error)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let i := Slice.len column
  if i != 1024#usize
  then ok (core.result.Result.Err r1_wire.Error.Public)
  else
    let pending_return ← host_semantic.check_base_column_loop column 0#usize
    match pending_return with
    | none => ok (core.result.Result.Ok ())
    | some r => ok r

theorem complete_result
  (column : Slice aspis_core.field.M31) :
  erase (produce column) = host_semantic.check_base_column column := by
  unfold produce host_semantic.check_base_column
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_060
