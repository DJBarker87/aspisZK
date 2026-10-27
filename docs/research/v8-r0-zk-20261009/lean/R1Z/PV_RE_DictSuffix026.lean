import R1Z.PV_RE_DictSuffix025
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_DictSuffix026
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.BinaryTree.multiproof`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_tree.BinaryTree) (indices : Slice Std.U32) (out : Payload (multiproof.LEAF_BITS)) : Result (Option (alloc.vec.Vec Std.U8)) := do
  let i := out
  let bits ← Aeneas.Std.lift (UScalar.cast .Usize i)
  let o ← host_tree.node_count indices
  let cf ← core.option.Option.Insts.CoreOpsTry_traitTry.branch o
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 32#usize val)
    let out := alloc.vec.Vec.with_capacity Std.U8 i1
    let level ← alloc.slice.Slice.to_vec core.clone.CloneU32 indices
    let out1 ← host_tree.multiproof_levels self out level 0#usize bits
    let i2 := alloc.vec.Vec.len out1
    let i3 ← Aeneas.Std.lift (Std.Usize.wrapping_mul 32#usize val)
    if i2 = i3
    then ok (some out1)
    else ok none
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual
      (alloc.vec.Vec Std.U8) residual


end R1Z.PV_RE_DictSuffix026
pv_dict_congr ProverRwFull.host_tree.BinaryTree.multiproof
pv_dict_congr R1Z.PV_RE_DictSuffix026.continueAfter
#print axioms R1Z.PV_RE_DictCore.ProverRwFull.host_tree.BinaryTree.multiproof
#print axioms R1Z.PV_RE_DictCore.R1Z.PV_RE_DictSuffix026.continueAfter
