import PV_L1_ResultCoercion
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
    let m ← Slice.index_usize column row
    if m >= aspis_core.field.P
    then ok (done (some (core.result.Result.Err r1_wire.Error.Public)))
    else let row1 ← Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize)
         ok (cont row1)
  else ok (done none)

theorem complete_result
  (column : Slice aspis_core.field.M31) (row : Std.Usize) :
  erase (produce column row) = host_semantic.check_base_column_loop.body column row := by
  unfold produce host_semantic.check_base_column_loop.body
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_059
