import PV_L1_ResultCoercion
import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace PV_L1_Source_064
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open PV_L1_Logged
variable [ExternalTypes] [ExternalFuns]

/-- Source-parametric phase entry and complete Result. Remaining loop and
opaque/native event edges are recorded in source-frontier.json. -/
def produce
  (claims : Array aspis_core.field.QM31 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  Logged aspis_core.field.QM31
  := do
  let _ ← observe .semanticCanonical 0 (ok ())
  let q ← aspis_core.field.QM31.ZERO
  let semantic := Array.repeat 16#usize q
  let mask_only := Array.repeat 10#usize q
  let (s, to_slice_mut_back) ← Aeneas.Std.lift (Array.to_slice_mut semantic)
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice aspis_core.field.QM31))
      claims { «end» := 16#usize }
  let s2 ←
    core.slice.Slice.copy_from_slice aspis_core.field.QM31.Insts.CoreMarkerCopy
      s s1
  let semantic1 := to_slice_mut_back s2
  let (s3, to_slice_mut_back1) ← Aeneas.Std.lift (Array.to_slice_mut mask_only)
  let s4 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice aspis_core.field.QM31))
      claims { start := 16#usize, «end» := 26#usize }
  let s5 ←
    core.slice.Slice.copy_from_slice aspis_core.field.QM31.Insts.CoreMarkerCopy
      s3 s4
  let mask_only1 := to_slice_mut_back1 s5
  let q1 ← Array.index_usize claims 27#usize
  aspis_core.state_only_hiding.state_only_selected_mask_value semantic1
    mask_only1 q1 point

theorem complete_result
  (claims : Array aspis_core.field.QM31 29#usize)
  (point : Array aspis_core.field.QM31 10#usize) :
  erase (produce claims point) = host_semantic.claim_mask_value claims point := by
  unfold produce host_semantic.claim_mask_value
  simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
  repeat' first
    | rfl
    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro value called
    | split <;> simp only [erase_bind,erase_observe,erase_lift,erase_coe,erase_pure]
#print axioms complete_result
end PV_L1_Source_064
