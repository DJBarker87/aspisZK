import R1Z.PV_RE_ComposedContextsGenerator
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ComposedSuffix028
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]
private abbrev Payload {α : Type} (_ : Result α) := α

/-- The actual entire suffix after the first bind in `host_tree.append_levels`.
Recursive calls remain the original extracted calls. -/
def continueAfter {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) (hash : H) (levels : alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) (depth : Std.Usize) (out : Payload (multiproof.LEAF_BITS)) : Result (alloc.vec.Vec (alloc.vec.Vec (Array Std.U8 32#usize))) := do
  let i := out
  let i1 ← Aeneas.Std.lift (UScalar.cast .Usize i)
  if depth = i1
  then ok levels
  else
    let v ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (alloc.vec.Vec
        (Array Std.U8 32#usize))) levels depth
    let s := alloc.vec.Vec.deref v
    let next ← host_tree.next_level aspis_coredigestDigest32Inst hash s
    let levels1 ← alloc.vec.Vec.push levels next
    let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add depth 1#usize)
    host_tree.append_levels aspis_coredigestDigest32Inst hash levels1 i2


end R1Z.PV_RE_ComposedSuffix028
pv_composed_source_contexts ProverRwFull.host_tree.append_levels
pv_composed_source_contexts R1Z.PV_RE_ComposedSuffix028.continueAfter
