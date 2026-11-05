import NGV_RowPayload
import NGV_SemanticArithmetic
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace NGV_SemanticCut
open AspisS1NativeCompact
abbrev Iter := core.ops.range.Range U8
abbrev State := Iter × Slice U8 × Usize × Usize
abbrev Exit := core.result.Result Unit compact.CodecError × Slice U8
def payload (ops : Ops) (input : Slice U8) (iter : Iter) (row : U8)
 (out : Slice U8) (src dst size : Usize) : Result (ControlFlow State Exit) := do
 let b ← compact.compact_row row
 if b then
  let half ← size/2#usize
  let sourceEnd ← src+half
  let source ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    input {start:=src,«end»:=sourceEnd}
  let outputEnd ← dst+size
  let (target,back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
    out {start:=dst,«end»:=outputEnd}
  let (reply,updated) ← ops.expandValues source target
  let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
  match cf with
  | core.ops.control_flow.ControlFlow.Continue _ => do
    let sourceEnd1 ← src+half
    ok (.cont (iter,back updated,sourceEnd1,outputEnd))
  | core.ops.control_flow.ControlFlow.Break residual => do
    let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame compact.CodecError) residual
    ok (.done (r,back updated))
 else
  let outputEnd ← dst+size
  let (target,back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
    out {start:=dst,«end»:=outputEnd}
  let sourceEnd ← src+size
  let source ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    input {start:=src,«end»:=sourceEnd}
  let updated ← core.slice.Slice.copy_from_slice core.marker.CopyU8 target source
  ok (.cont (iter,back updated,sourceEnd,outputEnd))
theorem cut (ops : Ops) (input out : Slice U8) (iter next : Iter)
 (row tag : U8) (size src dst : Usize)
 (iterator : core.iter.range.IteratorRange.next core.iter.range.StepU8 iter=ok (some row,next))
 (shape : r1_wire.row_shape row=ok (some (tag,size))) :
 compact.expand_semantic_loop.body ops input iter out src dst = (do
   let dstHead ← dst+5#usize
   let (header,back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
     out {start:=dst,«end»:=dstHead}
   let srcHead ← src+5#usize
   let sourceHeader ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
     input {start:=src,«end»:=srcHead}
   let header1 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 header sourceHeader
   payload ops input next row (back header1) srcHead dstHead size) := by
 simp only [compact.expand_semantic_loop.body,iterator,shape,bind_tc_ok,
   core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch]
 rfl
#print axioms cut
end NGV_SemanticCut
