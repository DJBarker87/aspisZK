import AspisV8R19.R479CallerBatchSlices
import AspisV8R19.R477BackedPointerWordImage

/-! Relate the actual modeled range-index result to the stored allocation cells
through the 64-bit pointer runtime. The explicit cells-equal-vector premise is
the memory image assumption; no wire decode or native caller theorem is made. -/
set_option autoImplicit false
namespace AspisV8R19.R480CallerPointerReads

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R475PointerWordRuntime
open AspisV8R19.R477BackedPointerWordImage
open AspisV8R19.R479CallerBatchSlices

private theorem first_success_bound (v : alloc.vec.Vec field.QM31)
    (s : Slice field.QM31) (h : selectedSlice v firstRange = .ok s) :
    388 ≤ v.val.length := by
  have hv : (do let out ← selectedSlice v firstRange; ok out.val) = .ok s.val := by
    rw [h]
    rfl
  rw [selectedSlice_values] at hv
  split at hv
  · simp [firstRange] at *
    omega
  · contradiction

private theorem second_success_bound (v : alloc.vec.Vec field.QM31)
    (s : Slice field.QM31) (h : selectedSlice v secondRange = .ok s) :
    417 ≤ v.val.length := by
  have hv : (do let out ← selectedSlice v secondRange; ok out.val) = .ok s.val := by
    rw [h]
    rfl
  rw [selectedSlice_values] at hv
  split at hv
  · simp [secondRange] at *
    omega
  · contradiction

private theorem view_first_eq (a : Allocation field.QM31)
    (v : alloc.vec.Vec field.QM31) (hcells : a.cells = v.val)
    (index : Nat) (hindex : index < 29) :
    (viewCells a 359 29).get ⟨index, by
      rw [view_length a 359 29 (by rw [hcells]; omega)]
      exact hindex⟩ = v.val[359 + index] := by
  rw [hcells]
  simp [viewCells, List.get_eq_getElem, List.getElem_take,
    List.getElem_drop, hindex]

private theorem view_second_eq (a : Allocation field.QM31)
    (v : alloc.vec.Vec field.QM31) (hcells : a.cells = v.val)
    (index : Nat) (hindex : index < 29) :
    (viewCells a 388 29).get ⟨index, by
      rw [view_length a 388 29 (by rw [hcells]; omega)]
      exact hindex⟩ = v.val[388 + index] := by
  rw [hcells]
  simp [viewCells, List.get_eq_getElem, List.getElem_take,
    List.getElem_drop, hindex]

theorem first_caller_pointer_read (heap : Heap field.QM31)
    (id : Nat) (a : Allocation field.QM31) (hlookup : heap id = some a)
    (v : alloc.vec.Vec field.QM31) (hcells : a.cells = v.val)
    (s : Slice field.QM31) (hslice : selectedSlice v firstRange = .ok s)
    (index : Nat) (hindex : index < 29) :
    (offset heap (encodePointer (backedPointer id a 359))
      (BitVec.ofNat 64 index)).bind
      (fun ptr => read heap (decodePointer ptr)) = s.val[index]? := by
  have hbound : 359 + 29 ≤ a.cells.length := by
    rw [hcells]
    have h := first_success_bound v s hslice
    simp [firstRange] at h
    omega
  have hfit : 359 ≤ a.cells.length := by omega
  have hword := backed_word_offset_read_view heap id a hlookup 359 29
    hbound index hindex
  rw [hword]
  rw [view_first_eq a v hcells index hindex]
  have hsource := firstRange_index v s hslice index hindex
  have hsourceBound : 359 + index < v.val.length := by omega
  rw [List.getElem?_eq_getElem hsourceBound] at hsource
  exact hsource.symm

theorem second_caller_pointer_read (heap : Heap field.QM31)
    (id : Nat) (a : Allocation field.QM31) (hlookup : heap id = some a)
    (v : alloc.vec.Vec field.QM31) (hcells : a.cells = v.val)
    (s : Slice field.QM31) (hslice : selectedSlice v secondRange = .ok s)
    (index : Nat) (hindex : index < 29) :
    (offset heap (encodePointer (backedPointer id a 388))
      (BitVec.ofNat 64 index)).bind
      (fun ptr => read heap (decodePointer ptr)) = s.val[index]? := by
  have hbound : 388 + 29 ≤ a.cells.length := by
    rw [hcells]
    have h := second_success_bound v s hslice
    simp [secondRange] at h
    omega
  have hfit : 388 ≤ a.cells.length := by omega
  have hword := backed_word_offset_read_view heap id a hlookup 388 29
    hbound index hindex
  rw [hword]
  rw [view_second_eq a v hcells index hindex]
  have hsource := secondRange_index v s hslice index hindex
  have hsourceBound : 388 + index < v.val.length := by omega
  rw [List.getElem?_eq_getElem hsourceBound] at hsource
  exact hsource.symm

#print axioms first_caller_pointer_read
#print axioms second_caller_pointer_read
end AspisV8R19.R480CallerPointerReads
