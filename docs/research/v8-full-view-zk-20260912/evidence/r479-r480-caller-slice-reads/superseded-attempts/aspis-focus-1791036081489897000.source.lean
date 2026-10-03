import AspisV8R19.R174GammaBatchStep

/-! The two selected public batch slices in the frozen callback, interpreted
through the pinned Aeneas Vec/Slice range-index model. This does not model wire
decoding or a native memory image. -/
set_option autoImplicit false
namespace AspisV8R19.R479CallerBatchSlices

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core

abbrev BatchRange := core.ops.range.Range Std.Usize

def firstRange : BatchRange :=
  { start := 359#usize, «end» := 388#usize }

def secondRange : BatchRange :=
  { start := 388#usize, «end» := 417#usize }

def selectedSlice (v : alloc.vec.Vec field.QM31) (r : BatchRange) :
    Result (Slice field.QM31) :=
  alloc.vec.Vec.index
    (core.slice.index.SliceIndexRangeUsizeSlice field.QM31) v r

theorem selectedSlice_values (v : alloc.vec.Vec field.QM31) (r : BatchRange) :
    (do
      let s ← selectedSlice v r
      ok s.val) =
    if r.start.val ≤ r.end.val ∧ r.end.val ≤ v.val.length then
      ok (v.val.slice r.start.val r.end.val)
    else fail .panic := by
  simp [selectedSlice, alloc.vec.Vec.index,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    UScalar.le_equiv, Slice.length]

private theorem selectedSlice_success_bounds
    (v : alloc.vec.Vec field.QM31) (r : BatchRange)
    (s : Slice field.QM31) (h : selectedSlice v r = .ok s) :
    r.start.val ≤ r.end.val ∧ r.end.val ≤ v.val.length := by
  simp [selectedSlice, alloc.vec.Vec.index,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    UScalar.le_equiv, Slice.length] at h
  exact h.1

private theorem selectedSlice_success_val
    (v : alloc.vec.Vec field.QM31) (r : BatchRange)
    (s : Slice field.QM31) (h : selectedSlice v r = .ok s) :
    s.val = v.val.slice r.start.val r.end.val := by
  simp [selectedSlice, alloc.vec.Vec.index,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    UScalar.le_equiv, Slice.length] at h
  exact congrArg Slice.val h.2

theorem firstRange_length (v : alloc.vec.Vec field.QM31) (s : Slice field.QM31)
    (h : selectedSlice v firstRange = .ok s) : s.val.length = 29 := by
  have hb := selectedSlice_success_bounds v firstRange s h
  have hv := selectedSlice_success_val v firstRange s h
  rw [hv]
  simp [firstRange, List.slice]
  omega

theorem secondRange_length (v : alloc.vec.Vec field.QM31) (s : Slice field.QM31)
    (h : selectedSlice v secondRange = .ok s) : s.val.length = 29 := by
  have hb := selectedSlice_success_bounds v secondRange s h
  have hv := selectedSlice_success_val v secondRange s h
  rw [hv]
  simp [secondRange, List.slice]
  omega

theorem firstRange_index (v : alloc.vec.Vec field.QM31) (s : Slice field.QM31)
    (h : selectedSlice v firstRange = .ok s) (index : Nat)
    (hindex : index < 29) : s.val[index]? = v.val[359 + index]? := by
  have hv := selectedSlice_success_val v firstRange s h
  have hb := selectedSlice_success_bounds v firstRange s h
  have hs : 359 + index < v.val.length := by
    have := hindex
    simp [firstRange] at hb
    simp [firstRange] at hv
    omega
  rw [hv]
  simp [firstRange, List.slice, List.getElem?_take, List.getElem?_drop, hindex]

theorem secondRange_index (v : alloc.vec.Vec field.QM31) (s : Slice field.QM31)
    (h : selectedSlice v secondRange = .ok s) (index : Nat)
    (hindex : index < 29) : s.val[index]? = v.val[388 + index]? := by
  have hv := selectedSlice_success_val v secondRange s h
  have hb := selectedSlice_success_bounds v secondRange s h
  have hs : 388 + index < v.val.length := by
    have := hindex
    simp [secondRange] at hb
    simp [secondRange] at hv
    omega
  rw [hv]
  simp [secondRange, List.slice, List.getElem?_take, List.getElem?_drop, hindex]

#print axioms selectedSlice_values
#print axioms firstRange_length
#print axioms secondRange_length
#print axioms firstRange_index
#print axioms secondRange_index
end AspisV8R19.R479CallerBatchSlices
