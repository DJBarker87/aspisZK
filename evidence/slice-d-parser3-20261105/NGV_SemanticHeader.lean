import NGV_SemanticCut
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticHeader
open AspisS1NativeCompact NGV_RowPayload NGV_ByteWindow
theorem result (ops : Ops) (input before : Slice U8) (iter next : NGV_SemanticCut.Iter)
 (row tag : U8) (src dst srcHead dstHead size : Usize)
 (live : row.val<27) (inputSize : input.val.length=7015) (outputSize : before.val.length=13831)
 (srcValue : src.val=NGD_SemanticSchedule.src row.val)
 (dstValue : dst.val=NGD_SemanticSchedule.dst row.val)
 (sourceValue : srcHead.val=src.val+5) (outputValue : dstHead.val=dst.val+5)
 (iterator : core.iter.range.IteratorRange.next core.iter.range.StepU8 iter=ok (some row,next))
 (shape : r1_wire.row_shape row=ok (some (tag,size))) :
 compact.expand_semantic_loop.body ops input iter before src dst=
 NGV_SemanticCut.payload ops input next row (middle input before row.val) srcHead dstHead size := by
 have bounds:=NGD_SemanticSchedule.windows row.val live
 have sourceWidth : srcHead.val-src.val=5 := by omega
 have outputWidth : dstHead.val-dst.val=5 := by omega
 have sourceRead : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   input {start:=src,«end»:=srcHead}=ok (select input src.val 5) := by
   simpa only [sourceWidth] using read input src srcHead (by constructor <;> omega)
 have targetRead : core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
   before {start:=dst,«end»:=dstHead}=
   ok (select before dst.val 5,fun x=>write before dst.val x) := by
   simpa only [outputWidth] using read_mut before dst dstHead (by constructor <;> omega)
 have copyRun:=copy (select before dst.val 5) (select input src.val 5) (by
   rw [select_length before dst.val 5 (by omega),select_length input src.val 5 (by omega)])
 rw [NGV_SemanticCut.cut ops input before iter next row tag size src dst iterator shape,
   NGV_SemanticArithmetic.add dst 5#usize dstHead (by simpa using outputValue),bind_tc_ok,targetRead]
 simp only [bind_tc_ok]
 change (src+5#usize >>= _) = _
 rw [NGV_SemanticArithmetic.add src 5#usize srcHead (by simpa using sourceValue),bind_tc_ok,
   sourceRead,bind_tc_ok,copyRun,bind_tc_ok]
 rw [srcValue,dstValue]
 rfl
#print axioms result
end NGV_SemanticHeader
