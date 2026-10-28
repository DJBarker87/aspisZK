import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_059
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (column : Slice aspis_core.field.M31) (row : Std.Usize) :
  Logged (ControlFlow Std.Usize (Option (core.result.Result Unit
    r1_wire.Error)))
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  if row < 1024#usize
  then
    let m ← PV_L1_Logged.lift (Slice.index_usize column row)
    if m >= aspis_core.field.P
    then Pure.pure (done (some (core.result.Result.Err r1_wire.Error.Public)))
    else let row1 ← Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize)
         Pure.pure (cont row1)
  else Pure.pure (done none)

theorem complete_result
  (column : Slice aspis_core.field.M31) (row : Std.Usize) :
  erase (produce column row) = host_semantic.check_base_column_loop.body column row := by
  unfold produce
  conv_rhs => unfold host_semantic.check_base_column_loop.body
  simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | with_reducible rfl
    | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
  all_goals
    cases value
    repeat' first
      | with_reducible rfl
      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro value called
      | split <;> simp only [PV_L1_EraseIf.erase_if,PV_L1_Projection.prod_case,Aeneas.Std.bind_tc_ok,erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
    all_goals rfl
#print axioms complete_result
end PV_L1_Source_059
