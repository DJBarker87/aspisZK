import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix014
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.claim_mask_value`.
Recursive calls remain the original extracted calls. -/
def continueAfter (claims : Array aspis_core.field.QM31 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result aspis_core.field.QM31 := do
  let q := out
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


end R1Z.PV_RE_NoCatchSuffix014
pv_no_catch_binds ProverRwFull.host_semantic.claim_mask_value
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix014.continueAfter

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix015
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_semantic.claims_at_point`.
Recursive calls remain the original extracted calls. -/
def continueAfter (columns : Array (alloc.vec.Vec aspis_core.field.QM31) 29#usize) (point : Array aspis_core.field.QM31 10#usize) (out : Payload (aspis_core.field.QM31.ZERO)) : Result (core.result.Result (Array aspis_core.field.QM31 29#usize)
    r1_wire.Error) := do
  let q := out
  let claims := Array.repeat 29#usize q
  let (claims1, pending_return) ←
    host_semantic.claims_at_point_loop columns point claims 0#usize
  match pending_return with
  | none => ok (core.result.Result.Ok claims1)
  | some r => ok r


end R1Z.PV_RE_NoCatchSuffix015
pv_no_catch_binds ProverRwFull.host_semantic.claims_at_point
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix015.continueAfter
