import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_062
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) :
  Logged (core.result.Result Unit r1_wire.Error)
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let pending_return ← PV_L1D_Logged.lift (host_semantic.check_base_columns_loop c1 0#usize)
  match pending_return with
  | none => Pure.pure (core.result.Result.Ok ())
  | some r => Pure.pure r

theorem complete_result
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) :
  erase (produce c1) = host_semantic.check_base_columns c1 := by
  unfold produce
  conv_rhs => unfold host_semantic.check_base_columns
  simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1D_EraseIf.erase_if,PV_L1D_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1D_Source_062
