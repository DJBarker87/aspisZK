import Aeneas
set_option autoImplicit false
namespace R1Z.ProverRw18SliceWrite
open Aeneas Aeneas.Std Result

def write (dest : Slice U8) (start stop : Usize) (src : Slice U8) : Result (Slice U8) := do
  let (segment,back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) dest ⟨start,stop⟩
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 segment src
  ok (back copied)

def put (dest : Slice U8) (start : Usize) (src : Slice U8) : Slice U8 :=
  ⟨dest.val.setSlice! start.val src.val,by
    simp only [List.length_setSlice!]; exact dest.property⟩

theorem exact_write (dest src : Slice U8) (start stop : Usize)
    (ordered : start.val≤stop.val) (bound : stop.val≤dest.val.length)
    (size : stop.val-start.val=src.val.length) :
    write dest start stop src=ok (put dest start src) := by
  have inside : start≤stop ∧ stop.val≤dest.length := ⟨ordered,bound⟩
  let segment : Slice U8 := ⟨dest.val.slice start.val stop.val,
    (dest.val.slice_length_le start.val stop.val).trans dest.property⟩
  have seglen : segment.length=stop.val-start.val := by
    simp only [segment,Slice.length,List.slice,List.length_take,List.length_drop]
    omega
  have length : Slice.len segment=Slice.len src := by
    apply UScalar.eq_of_val_eq
    simp only [Slice.len_val,seglen,Slice.length]
    exact size
  unfold write core.slice.index.Slice.index_mut core.slice.index.SliceIndexRangeUsizeSlice
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  simp only [inside,if_true,bind_tc_ok,Aeneas.Std.uncurry]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 segment src
    ok (⟨dest.val.setSlice! start.val copied.val,_⟩ : Slice U8))=_
  simp only [core.slice.Slice.copy_from_slice,length,if_true,bind_tc_ok]
  rfl

#print axioms exact_write
end R1Z.ProverRw18SliceWrite
