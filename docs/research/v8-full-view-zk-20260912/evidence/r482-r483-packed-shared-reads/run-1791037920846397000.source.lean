import AspisV8R19.R432PointerPrimitive
import AspisV8R19.R481NativeQM31Cell

/-! Storage refinement for the explicit allocation model: map stored values
through a representation function while preserving addresses and bounds. This
is a model theorem, not a native source or allocation theorem. -/
set_option autoImplicit false
namespace AspisV8R19.R482PackedAllocationRead

open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R481NativeQM31Cell
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core

def mapAllocation {A B : Type} (f : A → B) (a : Allocation A) : Allocation B :=
  { base := a.base
    cells := a.cells.map f
    nonzero := a.nonzero
    aligned := a.aligned
    small := by simpa only [List.length_map] using a.small
    noWrap := by simpa only [List.length_map] using a.noWrap }

def mapHeap {A B : Type} (f : A → B) (heap : Heap A) : Heap B :=
  fun id => (heap id).map (mapAllocation f)

theorem read_map {A B : Type} (f : A → B) (heap : Heap A)
    (ptr : Pointer) :
    (read heap ptr).map f = read (mapHeap f heap) ptr := by
  cases ho : ptr.origin with
  | none => simp [read, mapHeap, ho]
  | some origin =>
    rcases origin with ⟨id, offset⟩
    cases ha : heap id with
    | none => simp [read, mapHeap, ho, ha]
    | some a =>
      by_cases hc : ptr.address = a.base + offset ∧ offset % 16 = 0
      · simp [read, mapHeap, mapAllocation, ho, ha, hc,
          List.getElem?_map]
      · simp [read, mapHeap, mapAllocation, ho, ha, hc]

theorem mapHeap_decode_encode (heap : Heap field.QM31) :
    mapHeap decodeQM31 (mapHeap encodeQM31 heap) = heap := by
  funext id
  cases h : heap id with
  | none => simp [mapHeap, h]
  | some a =>
    have hcells : (a.cells.map encodeQM31).map decodeQM31 = a.cells := by
      simp [List.map_map, Function.comp_def, decodeQM31_encodeQM31]
    cases a with
    | mk base cells nonzero aligned small noWrap =>
      simp [mapHeap, mapAllocation, h, hcells]

theorem read_packed_roundtrip (heap : Heap field.QM31) (ptr : Pointer) :
    (read (mapHeap encodeQM31 heap) ptr).map decodeQM31 = read heap ptr := by
  have h := read_map decodeQM31 (mapHeap encodeQM31 heap) ptr
  rw [mapHeap_decode_encode] at h
  exact h

#print axioms mapAllocation
#print axioms mapHeap
#print axioms read_map
#print axioms mapHeap_decode_encode
#print axioms read_packed_roundtrip
end AspisV8R19.R482PackedAllocationRead
