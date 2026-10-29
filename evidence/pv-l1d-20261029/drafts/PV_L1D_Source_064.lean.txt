import PV_L1D_ResultCoercion
import PV_L1D_Projection
import PV_L1D_EraseIf
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1D_Source_064
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (claims : Array aspis_core.field.QM31 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← PV_L1D_Logged.lift (aspis_core.field.QM31.ZERO)
  let semantic := Array.repeat 16#usize q
  let mask_only := Array.repeat 10#usize q
  let (s, to_slice_mut_back) ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice_mut semantic))
  let s1 ← PV_L1D_Logged.lift (core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      claims { «end» := 16#usize })
  let s2 ← PV_L1D_Logged.lift (core.slice.Slice.copy_from_slice aspis_core.field.QM31.Insts.CoreMarkerCopy
      s s1)
  let semantic1 := to_slice_mut_back s2
  let (s3, to_slice_mut_back1) ← PV_L1D_Logged.lift (Aeneas.Std.lift (Array.to_slice_mut mask_only))
  let s4 ← PV_L1D_Logged.lift (core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      claims { start := 16#usize, «end» := 26#usize })
  let s5 ← PV_L1D_Logged.lift (core.slice.Slice.copy_from_slice aspis_core.field.QM31.Insts.CoreMarkerCopy
      s3 s4)
  let mask_only1 := to_slice_mut_back1 s5
  let q1 ← PV_L1D_Logged.lift (Array.index_usize claims 27#usize)
  aspis_core.state_only_hiding.state_only_selected_mask_value semantic1
    mask_only1 q1 point

theorem complete_result
  (claims : Array aspis_core.field.QM31 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  erase (produce claims point) = host_semantic.claim_mask_value claims point := by
  unfold produce
  conv_rhs => unfold host_semantic.claim_mask_value
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
end PV_L1D_Source_064
