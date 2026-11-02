import NEO_WindowV2.Funs
import NEO_ByteCuts
set_option autoImplicit false
namespace NEO_ComplexCells
open Aeneas Aeneas.Std Result
attribute [local irreducible] core.num.U32.from_le_bytes

def bytes (a b c d e f g h : U8) : Slice U8 :=
 (Array.make 8#usize [a,b,c,d,e,f,g,h]).to_slice

theorem first (a b c d e f g h : U8) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  (bytes a b c d e f g h) {start:=0#usize,«end»:=4#usize}=
 ok (Array.make 4#usize [a,b,c,d]).to_slice := by
 simp [bytes,core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index,
  Array.to_slice,Array.make,Slice.length,List.slice]

theorem second (a b c d e f g h : U8) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  (bytes a b c d e f g h) {start:=4#usize,«end»:=8#usize}=
 ok (Array.make 4#usize [e,f,g,h]).to_slice := by
 simp [bytes,core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index,
  Array.to_slice,Array.make,Slice.length,List.slice]

theorem word0 (a b c d e f g h : U8) :
 NEO_WindowV2.word (bytes a b c d e f g h) 0#usize =
 ok (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])) := by
 simp [NEO_WindowV2.word,bytes,Slice.index_usize,Array.to_slice,Array.make,lift,bind_tc_ok]

theorem word4 (a b c d e f g h : U8) :
 NEO_WindowV2.word (bytes a b c d e f g h) 4#usize =
 ok (core.num.U32.from_le_bytes (Array.make 4#usize [e,f,g,h])) := by
 simp [NEO_WindowV2.word,bytes,Slice.index_usize,Array.to_slice,Array.make,lift,bind_tc_ok]

#print axioms first
#print axioms second
#print axioms word0
#print axioms word4
end NEO_ComplexCells
