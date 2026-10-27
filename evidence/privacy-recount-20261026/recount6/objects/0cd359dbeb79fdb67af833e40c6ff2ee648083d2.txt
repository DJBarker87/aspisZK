import R1Z.ProverRwOuterContext
set_option autoImplicit false
namespace R1Z.ProverRwOuterWrite
open Aeneas Aeneas.Std Result

def write {N M : Usize} (dest : Array U8 N) (start stop : Usize) (src : Array U8 M) :
    Result (Array U8 N) := do
  let (s,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) dest ⟨start,stop⟩
  let input ← lift (Array.to_slice src)
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s input
  .ok (back copied)

def put {N M : Usize} (dest : Array U8 N) (start : Usize) (src : Array U8 M) : Array U8 N :=
  ⟨dest.val.setSlice! start.val src.val,by simp [dest.property]⟩

theorem write_exact {N M : Usize} (dest : Array U8 N) (start stop : Usize)
    (src : Array U8 M) (ordered : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (size : stop.val-start.val=M.val) :
    write dest start stop src = .ok (put dest start src) := by
  have inside : start ≤ stop ∧ stop.val ≤ (Array.to_slice dest).length := by
    exact ⟨ordered,by simpa [Array.to_slice,dest.property] using bound⟩
  let segment : Slice U8 := ⟨dest.val.slice start.val stop.val,by
    have h := dest.val.slice_length_le start.val stop.val
    have hd : dest.val.length ≤ Usize.max := (Array.to_slice dest).property
    exact h.trans hd⟩
  have seglen : segment.length = stop.val-start.val := by
    simp only [segment,Slice.length,List.slice,List.length_take,List.length_drop]
    have hd := dest.property
    omega
  have length : Slice.len segment = Slice.len (Array.to_slice src) := by
    apply UScalar.eq_of_val_eq
    simp only [Slice.len_val,seglen,Slice.length,Array.to_slice]
    exact size.trans src.property.symm
  unfold write core.array.Array.index_mut core.ops.index.IndexMutSlice
    core.slice.index.SliceIndexRangeUsizeSlice core.slice.index.Slice.index_mut
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  simp only [inside,if_true,bind_tc_ok,lift,Aeneas.Std.uncurry]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 segment (Array.to_slice src)
    .ok (Array.from_slice dest ⟨dest.val.setSlice! start.val copied.val,by
      simp only [List.length_setSlice!]; exact (Array.to_slice dest).property⟩)) = _
  simp only [core.slice.Slice.copy_from_slice,length,if_true,bind_tc_ok]
  unfold Array.from_slice
  simp only [Array.to_slice,List.length_setSlice!,dest.property,if_pos rfl]
  rfl

#print axioms write_exact
end R1Z.ProverRwOuterWrite
