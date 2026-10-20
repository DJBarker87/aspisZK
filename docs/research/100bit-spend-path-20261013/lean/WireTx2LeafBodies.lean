import WireTx2Records
import WireTx2SliceFacts
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2
/-- The three opaque operations plus typed salt-conversion boundary in the emitted batch-leaf body. -/
structure LeafOps where
  salt : Slice U8 → Result (Array U8 32#usize)
  c1Tag : Result U8
  c2Tag : Result U8
  leaf : {H : Type} → aspis_core.digest.Digest32 H → H → U8 → Slice U8 → Array U8 32#usize → Result (Array U8 32#usize)

def verifier.candidate.batch_leafWithWireOps
  (ops : LeafOps)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (tree : Std.Usize) (q : Slice Std.U8) :
  Result (Array Std.U8 32#usize)
  := do
  match tree.val with
  | 0 =>
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) q { start := 608#usize, «end» := 640#usize }
    let salt ← ops.salt s
    let s1 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) q
        { «end» := 480#usize }
    let i ← ops.c1Tag
    ops.leaf
      aspis_coredigestDigest32Inst hash i s1 salt
  | 1 =>
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) q { start := 640#usize, «end» := 672#usize }
    let salt ← ops.salt s
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) q { start := 480#usize, «end» := 608#usize }
    let i ← ops.c2Tag
    ops.leaf
      aspis_coredigestDigest32Inst hash i s1 salt
  | _ =>
    let s ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) q { start := 800#usize, «end» := 832#usize }
    let salt ← ops.salt s
    let s1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U8) q { start := 672#usize, «end» := 800#usize }
    ops.leaf
      aspis_coredigestDigest32Inst hash 114#u8 s1 salt


end AspisR1Stage2
