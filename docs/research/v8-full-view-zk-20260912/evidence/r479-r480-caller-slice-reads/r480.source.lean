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

theorem first_caller_pointer_read (heap : Heap field.QM31)
    (id : Nat) (a : Allocation field.QM31) (hlookup : heap id = some a)
    (v : alloc.vec.Vec field.QM31) (hcells : a.cells = v.val)
    (s : Slice field.QM31) (hslice : selectedSlice v firstRange = .ok s)
    (index : Nat) (hindex : index < 29) :
    (offset heap (encodePointer (backedPointer id a 359))
      (BitVec.ofNat 64 index)).bind
      (fun ptr => read heap (decodePointer ptr)) = s.val[index]? := by
  have himage := selectedSlice_success_image v firstRange s hslice
  have hbound : 359 + 29 ≤ a.cells.length := by
    have hb := himage.2.1
    simp [firstRange] at hb
    rw [hcells]
    omega
  have hview : viewCells a 359 29 = s.val := by
    simpa [viewCells, List.slice, hcells, firstRange] using himage.2.2.symm
  have hi : index < (viewCells a 359 29).length := by
    rw [view_length a 359 29 hbound]
    exact hindex
  have hword := backed_word_offset_read_view heap id a hlookup 359 29
    hbound index hindex
  calc
    _ = some ((viewCells a 359 29)[index]) := by
      simpa only [List.get_eq_getElem] using hword
    _ = (viewCells a 359 29)[index]? := (List.getElem?_eq_getElem hi).symm
    _ = s.val[index]? := by rw [hview]


theorem second_caller_pointer_read (heap : Heap field.QM31)
    (id : Nat) (a : Allocation field.QM31) (hlookup : heap id = some a)
    (v : alloc.vec.Vec field.QM31) (hcells : a.cells = v.val)
    (s : Slice field.QM31) (hslice : selectedSlice v secondRange = .ok s)
    (index : Nat) (hindex : index < 29) :
    (offset heap (encodePointer (backedPointer id a 388))
      (BitVec.ofNat 64 index)).bind
      (fun ptr => read heap (decodePointer ptr)) = s.val[index]? := by
  have himage := selectedSlice_success_image v secondRange s hslice
  have hbound : 388 + 29 ≤ a.cells.length := by
    have hb := himage.2.1
    simp [secondRange] at hb
    rw [hcells]
    omega
  have hview : viewCells a 388 29 = s.val := by
    simpa [viewCells, List.slice, hcells, secondRange] using himage.2.2.symm
  have hi : index < (viewCells a 388 29).length := by
    rw [view_length a 388 29 hbound]
    exact hindex
  have hword := backed_word_offset_read_view heap id a hlookup 388 29
    hbound index hindex
  calc
    _ = some ((viewCells a 388 29)[index]) := by
      simpa only [List.get_eq_getElem] using hword
    _ = (viewCells a 388 29)[index]? := (List.getElem?_eq_getElem hi).symm
    _ = s.val[index]? := by rw [hview]


#print axioms first_caller_pointer_read
#print axioms second_caller_pointer_read
end AspisV8R19.R480CallerPointerReads
