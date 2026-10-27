import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix057
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.initial_mask_value`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (row : Std.Usize) (out : Payload (host_semantic.boolean_point row)) : Result aspis_core.field.QM31 := do
  let point := out
  let q ← aspis_core.field.QM31.ZERO
  let semantic := Array.repeat 16#usize q
  let mask_only := Array.repeat 10#usize q
  let semantic1 ←
    host_semantic.initial_mask_value_loop0 columns row semantic 0#usize
  let mask_only1 ←
    host_semantic.initial_mask_value_loop1 columns row mask_only 0#usize
  let v ← Array.index_usize columns 27#usize
  let q1 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.QM31) v row
  aspis_core.state_only_hiding.state_only_selected_mask_value semantic1
    mask_only1 q1 point


end R1Z.PV_RE_NoCatchSuffix057
pv_no_catch_binds ProverRwFull.host_semantic.initial_mask_value
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix057.continueAfter
