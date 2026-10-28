import PV_L1_ResultCoercion
import PV_L1_Projection
import PV_L1_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_050
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (row : Std.Usize) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let point ← PV_L1_Logged.lift (host_semantic.boolean_point row)
  let q ← PV_L1_Logged.lift (aspis_core.field.QM31.ZERO)
  let semantic := Array.repeat 16#usize q
  let mask_only := Array.repeat 10#usize q
  let semantic1 ← PV_L1_Logged.lift (host_semantic.initial_mask_value_loop0 columns row semantic 0#usize)
  let mask_only1 ← PV_L1_Logged.lift (host_semantic.initial_mask_value_loop1 columns row mask_only 0#usize)
  let v ← PV_L1_Logged.lift (Array.index_usize columns 27#usize)
  let q1 ← PV_L1_Logged.lift (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.QM31) v row)
  aspis_core.state_only_hiding.state_only_selected_mask_value semantic1
    mask_only1 q1 point

theorem complete_result
  (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize)
  (row : Std.Usize) :
  erase (produce columns row) = host_semantic.initial_mask_value columns row := by
  unfold produce
  conv_rhs => unfold host_semantic.initial_mask_value
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
end PV_L1_Source_050
