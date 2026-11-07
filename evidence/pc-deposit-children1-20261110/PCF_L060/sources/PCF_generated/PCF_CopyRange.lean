import PCF_SliceFrame
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_CopyRange

def write (data src : Slice U8) (r : core.ops.range.Range Usize) : Result (Slice U8) := do
  let (window, back) ← core.slice.index.SliceIndexRangeUsizeSlice.index_mut r data
  let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window src
  ok (back copied)

theorem result (data src : Slice U8) (r : core.ops.range.Range Usize)
    (bounds : r.start ≤ r.«end» ∧ r.«end».val ≤ data.length)
    (width : src.length = r.«end».val - r.start.val) :
    write data src r = ok (data.setSlice! r.start.val src.val) := by
  have hlen : (data.val.slice r.start.val r.«end».val).length = src.length := by
    have hs : r.start.val ≤ r.«end».val := by scalar_tac
    have he : r.«end».val ≤ data.val.length := bounds.2
    simp only [List.slice, List.length_take, List.length_drop]
    omega
  have heq : (Slice.len (⟨data.val.slice r.start.val r.«end».val,
      by have := data.property; simp only [List.slice, List.length_take, List.length_drop]; omega⟩ : Slice U8)) = src.len := by
    apply UScalar.eq_of_val_eq
    exact hlen
  simp only [write, core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    if_pos bounds, bind_tc_ok, core.slice.Slice.copy_from_slice]
  change (do
    let copied ← (if (⟨data.val.slice r.start.val r.«end».val, by have := data.property; simp only [List.slice, List.length_take, List.length_drop]; omega⟩ : Slice U8).len = src.len then ok src else .fail .panic)
    ok (data.setSlice! r.start.val copied.val)) = _
  rw [if_pos heq]
  rfl

#print axioms result
end PCF_CopyRange
