import PV_L2C_ParserSlices
set_option autoImplicit false
namespace PV_L2C_ParserHalves8
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71
#print core.slice.index.SliceIndexRangeUsizeSlice.index

open PV_L2C_ParserSlices

def pair (a b : Array U8 8#usize) : Slice U8 :=
  ⟨a.val++b.val,by
    have ha := a.property
    have hb := b.property
    simp only [List.length_append]
    scalar_tac⟩

theorem left (a b : Array U8 8#usize) :
    core.slice.index.SliceIndexRangeUsizeSlice.index {start:=0#usize,«end»:=8#usize} (pair a b)=
      ok (slice a) := by
  have ha : a.val.length=8 := a.property
  have hb : b.val.length=8 := b.property
  simp [core.slice.index.SliceIndexRangeUsizeSlice.index,pair,slice,List.slice,ha,hb]
#print axioms left

theorem right (a b : Array U8 8#usize) :
    core.slice.index.SliceIndexRangeUsizeSlice.index {start:=8#usize,«end»:=16#usize} (pair a b)=
      ok (slice b) := by
  have ha : a.val.length=8 := a.property
  have hb : b.val.length=8 := b.property
  simp [core.slice.index.SliceIndexRangeUsizeSlice.index,pair,slice,List.slice,ha,hb]
  apply Subtype.ext
  change b.val.take 8=b.val
  exact List.take_of_length_le (Nat.le_of_eq hb)
#print axioms right
end PV_L2C_ParserHalves8
