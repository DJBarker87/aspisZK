import NEO_QuadraticCuts
set_option autoImplicit false
namespace NEO_FixedWindow
open Aeneas Aeneas.Std Result

def window (bytes : Slice U8) (offset : Nat) (n : Usize)
 (bound : offset+n.val≤bytes.val.length) : Array U8 n :=
 ⟨(bytes.val.drop offset).take n.val,by simp only [List.length_take,List.length_drop]; omega⟩

theorem range (bytes : Slice U8) (start finish n : Usize)
 (order : start.val≤finish.val) (fit : finish.val≤bytes.val.length)
 (width : finish.val-start.val=n.val) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
 bytes {start:=start,«end»:=finish}=
 ok (window bytes start.val n (by omega)).to_slice := by
 simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index,
  Slice.length,order,fit,window,Array.to_slice,List.slice,width]

#print axioms range
end NEO_FixedWindow
