import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_001
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (out : alloc.vec.Vec Std.U8)
  (row : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  Logged (alloc.vec.Vec Std.U8)
  := do
  let _ ← observe .publication 0 (ok ())
  let out1 ← PV_L1D_Logged.lift (prover.append_opening_base_row_loop out row 0#usize)
  let we ← PV_L1D_Logged.lift (Array.index_usize row 28#usize)
  let bytes ← PV_L1D_Logged.lift (aspis_core.field.wide_exact.WideExact.to_le_bytes we)
  let s ← PV_L1D_Logged.lift (core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes
      { «end» := 16#usize })
  alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out1 s

theorem complete_result
  (out : alloc.vec.Vec Std.U8)
  (row : Array aspis_core.field.wide_exact.WideExact 29#usize) :
  erase (produce out row) = prover.append_opening_base_row out row := by
  unfold produce
  conv_rhs => unfold prover.append_opening_base_row
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
end PV_L1D_Source_001
