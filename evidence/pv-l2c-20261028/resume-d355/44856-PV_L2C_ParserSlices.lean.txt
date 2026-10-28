import PV_L2C_CanonicalParser
set_option autoImplicit false
namespace PV_L2C_ParserSlices
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71
#print core.slice.index.SliceIndexRangeUsizeSlice.index

def slice {n : Usize} (a : Array U8 n) : Slice U8 :=
  ⟨a.val,by have := a.property; scalar_tac⟩

theorem copy_array {n : Usize} (a : Array U8 n) :
    core.array.TryFromArrayCopySlice.try_from n core.marker.CopyU8 (slice a)=ok (.Ok a) := by
  simp [core.array.TryFromArrayCopySlice.try_from,slice,a.property]
#print axioms copy_array

def pair (a b : Array U8 4#usize) : Slice U8 :=
  ⟨a.val++b.val,by
    have ha := a.property
    have hb := b.property
    simp only [List.length_append]
    scalar_tac⟩

theorem left (a b : Array U8 4#usize) :
    core.slice.index.SliceIndexRangeUsizeSlice.index {start:=0#usize,«end»:=4#usize} (pair a b)=
      ok (slice a) := by
  have ha : a.val.length=4 := a.property
  have hb : b.val.length=4 := b.property
  simp [core.slice.index.SliceIndexRangeUsizeSlice.index,pair,slice,List.slice,ha,hb]
#print axioms left

theorem right (a b : Array U8 4#usize) :
    core.slice.index.SliceIndexRangeUsizeSlice.index {start:=4#usize,«end»:=8#usize} (pair a b)=
      ok (slice b) := by
  have ha : a.val.length=4 := a.property
  have hb : b.val.length=4 := b.property
  simp [core.slice.index.SliceIndexRangeUsizeSlice.index,pair,slice,List.slice,ha,hb]
  apply Subtype.ext
  change b.val.take 4=b.val
  exact List.take_of_length_le (Nat.le_of_eq hb)
#print axioms right
end PV_L2C_ParserSlices
