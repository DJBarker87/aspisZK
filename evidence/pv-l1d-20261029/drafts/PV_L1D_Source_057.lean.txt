import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_057
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (column : Array aspis_core.field.QM31 1024#usize) (row : Std.Usize) :
  Logged (ControlFlow Std.Usize (Option (core.result.Result Unit
    r1_wire.Error)))
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  if row < 1024#usize
  then
    let b := Array.repeat 16#usize 0#u8
    let q ← PV_L1D_Logged.lift (Array.index_usize column row)
    let (s, to_slice_mut_back) ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice_mut b))
    let s1 ← PV_L1D_Logged.lift (aspis_core.field.QM31.write_le_bytes q s)
    let b1 := to_slice_mut_back s1
    let s2 ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice b1))
    let o ← PV_L1D_Logged.lift (aspis_core.field.QM31.from_le_bytes s2)
    let b2 := core.option.Option.is_none o
    if b2
    then Pure.pure (done (some (core.result.Result.Err r1_wire.Error.Public)))
    else let row1 ← Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize)
         Pure.pure (cont row1)
  else Pure.pure (done none)

theorem complete_result
  (column : Array aspis_core.field.QM31 1024#usize) (row : Std.Usize) :
  erase (produce column row) = host_semantic.check_secure_column_loop.body column row := by
  unfold produce
  conv_rhs => unfold host_semantic.check_secure_column_loop.body
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
end PV_L1D_Source_057
