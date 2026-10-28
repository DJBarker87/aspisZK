import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_062
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) :
  Logged (core.result.Result Unit r1_wire.Error)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let pending_return ← PV_L1_Logged.lift (host_semantic.check_base_columns_loop c1 0#usize)
  match pending_return with
  | none => ok (core.result.Result.Ok ())
  | some r => ok r

theorem complete_result
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) :
  erase (produce c1) = host_semantic.check_base_columns c1 := by
  unfold produce host_semantic.check_base_columns
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_062
