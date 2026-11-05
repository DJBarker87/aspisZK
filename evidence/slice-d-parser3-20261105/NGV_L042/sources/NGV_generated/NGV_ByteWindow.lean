import NGV_Monad
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ByteWindow
def select (bytes : Slice U8) (start width : Nat) : Slice U8 :=
 ⟨(bytes.val.drop start).take width,by
   have h:=bytes.property;simp only [List.length_take,List.length_drop];omega⟩
def write (out : Slice U8) (start : Nat) (bytes : Slice U8) : Slice U8 :=
 out.setSlice! start bytes.val
theorem select_length (bytes : Slice U8) (start width : Nat) (fit : start+width≤bytes.val.length) :
 (select bytes start width).val.length=width := by
 simp only [select,List.length_take,List.length_drop];omega
theorem write_length (out bytes : Slice U8) (start : Nat) :
 (write out start bytes).val.length=out.val.length := by
 exact Slice.setSlice!_length out start bytes.val
theorem read (bytes : Slice U8) (start finish : Usize)
 (fit : start.val≤finish.val ∧ finish.val≤bytes.val.length) :
 core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   bytes {start,«end»:=finish}=ok (select bytes start.val (finish.val-start.val)) := by
 simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
   core.slice.index.SliceIndexRangeUsizeSlice.index]
 rw [dif_pos fit]
 rfl
theorem read_mut (bytes : Slice U8) (start finish : Usize)
 (fit : start.val≤finish.val ∧ finish.val≤bytes.val.length) :
 core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
   bytes {start,«end»:=finish}=
 ok (select bytes start.val (finish.val-start.val),fun after=>write bytes start.val after) := by
 simp only [core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeUsizeSlice,
   core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
 rw [dif_pos fit]
 rfl
theorem copy (destination source : Slice U8) (same : destination.val.length=source.val.length) :
 core.slice.Slice.copy_from_slice core.marker.CopyU8 destination source=ok source := by
 unfold core.slice.Slice.copy_from_slice
 have sameLen : Slice.len destination=Slice.len source := UScalar.eq_of_val_eq same
 simp [sameLen]
#print axioms select_length
#print axioms write_length
#print axioms read
#print axioms read_mut
#print axioms copy
end NGV_ByteWindow
