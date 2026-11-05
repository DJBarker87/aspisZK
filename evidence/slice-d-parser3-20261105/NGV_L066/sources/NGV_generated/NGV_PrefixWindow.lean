import NGV_ByteWindow
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_PrefixWindow
open NGV_ByteWindow
theorem read (bytes : Slice U8) (width : Usize) (fit : width.val≤bytes.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   bytes {«end»:=width}=ok (select bytes 0 width.val) := by
 simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
   core.slice.index.SliceIndexRangeToUsizeSlice.index,fit,select,List.slice]
theorem read_mut (bytes : Slice U8) (width : Usize) (fit : width.val≤bytes.val.length) :
 core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   bytes {«end»:=width}=ok (select bytes 0 width.val,fun after=>write bytes 0 after) := by
 simp [core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeToUsizeSlice,
   core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,fit,select,write,List.slice]
#print axioms read
#print axioms read_mut
end NGV_PrefixWindow
