import R1Z.PV_RunJoin_PostBind62
import R1Z.PV_RJN_Bytes
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SliceBound62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41

theorem range (logical : Slice U8) (first last : Usize) :
    Post (fun s => s.length≤logical.length)
      (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        logical {start:=first, «end»:=last}) := by
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index]
  split
  · change (List.slice first.val last.val logical.val).length≤logical.length
    simp only [List.slice,List.length_take,List.length_drop]
    change min (last.val-first.val) (logical.length-first.val)≤logical.length
    omega
  · trivial

theorem rangeTo (logical : Slice U8) (last : Usize) :
    Post (fun s => s.length≤logical.length)
      (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        logical {«end»:=last}) := by
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index]
  split
  · change (List.slice 0 last.val logical.val).length≤logical.length
    simp only [List.slice,List.length_take,List.length_drop,Nat.sub_zero]
    change min last.val logical.length≤logical.length
    omega
  · trivial

theorem append (out : alloc.vec.Vec U8) (s : Slice U8) :
    Post (fun next => next.length=out.length+s.length)
      (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s) := by
  cases h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s with
  | fail e => trivial
  | div => trivial
  | ok next =>
    have hv := PV_RJN_Bytes.append_success out s next h
    change next.val.length=out.val.length+s.val.length
    rw [hv,List.length_append]

#print axioms range
#print axioms rangeTo
#print axioms append
end R1Z.PV_RunJoin_SliceBound62
