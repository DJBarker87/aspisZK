import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix027
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.BinaryTree.root`.
Recursive calls remain the original extracted calls. -/
def continueAfter (self : host_tree.BinaryTree) (out : Payload (multiproof.LEAF_BITS)) : Result (Array Std.U8 32#usize) := do
  let i := out
  let i1 ← Aeneas.Std.lift (UScalar.cast .Usize i)
  let v ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec
      (Array Std.U8 32#usize))) self.levels i1
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
    32#usize)) v 0#usize


end R1Z.PV_RE_ComposedSuffix027
pv_composed_source_contexts ProverRwFull.host_tree.BinaryTree.root
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix027.continueAfter
