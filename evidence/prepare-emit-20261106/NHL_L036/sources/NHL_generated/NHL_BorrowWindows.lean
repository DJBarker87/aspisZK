import NHL_Packets
set_option autoImplicit false
namespace AspisR1.NHL_BorrowWindows
open Aeneas Aeneas.Std Result

theorem left (v : alloc.vec.Vec U8) (s : Slice U8) (cut : Usize)
 (bound : cut.val≤v.val.length) (bytes : v.val.take cut.val=s.val) :
 alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) v {«end»:=cut}=ok s := by
 simp only [alloc.vec.Vec.index,core.slice.index.SliceIndexRangeToUsizeSlice,
   core.slice.index.SliceIndexRangeToUsizeSlice.index]
 rw [if_pos bound]
 congr 1
 apply Subtype.ext
 simpa only [List.slice,List.drop_zero,Nat.sub_zero] using bytes

theorem right (v : alloc.vec.Vec U8) (s : Slice U8) (cut : Usize)
 (bound : cut.val≤v.val.length) (bytes : v.val.drop cut.val=s.val) :
 alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) v {start:=cut}=ok s := by
 simp only [alloc.vec.Vec.index,core.slice.index.SliceIndexRangeFromUsizeSlice,
   core.slice.index.SliceIndexRangeFromUsizeSlice.index]
 rw [if_pos bound]
 congr 1
 apply Subtype.ext
 exact bytes
#print axioms left
#print axioms right
end AspisR1.NHL_BorrowWindows
