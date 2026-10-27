import R1Z.PV_RE_NoCatchGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_NoCatchSuffix064
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.node_count`.
Recursive calls remain the original extracted calls. -/
def continueAfter (indices : Slice Std.U32) (out : Payload (host_tree.check_indices indices)) : Result (Option Std.Usize) := do
  let o := out
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let level := Array.repeat 16#usize 0#u32
    let i := Slice.len indices
    let (s, index_mut_back) ←
      core.array.Array.index_mut (core.ops.index.IndexMutSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U32)) level
        { «end» := i }
    let s1 ← core.slice.Slice.copy_from_slice core.marker.CopyU32 s indices
    let level1 := index_mut_back s1
    let i1 := Slice.len indices
    let i2 ← multiproof.LEAF_BITS
    let i3 ← host_tree.count_levels level1 i1 0#u32 0#usize i2
    ok (some i3)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      Std.Usize residual


end R1Z.PV_RE_NoCatchSuffix064
pv_no_catch_binds ProverRwFull.host_tree.node_count
pv_no_catch_binds R1Z.PV_RE_NoCatchSuffix064.continueAfter
