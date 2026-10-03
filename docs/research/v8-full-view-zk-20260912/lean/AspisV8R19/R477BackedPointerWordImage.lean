import AspisV8R19.R475PointerWordRuntime

/-! Representable image of backed allocation pointers in the 64-bit word model.
These are arithmetic and allocation-view facts, not source-semantics claims. -/
set_option autoImplicit false
namespace AspisV8R19.R477BackedPointerWordImage
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R475PointerWordRuntime

def encodePointer (ptr : Pointer) : WordPointer :=
  ⟨BitVec.ofNat 64 ptr.address, ptr.origin⟩

theorem decode_encode (ptr : Pointer) (haddress : ptr.address < 2 ^ 64) :
    decodePointer (encodePointer ptr) = ptr := by
  cases ptr with
  | mk address origin =>
    simp [encodePointer, decodePointer, BitVec.toNat_ofNat]
    exact haddress

theorem backed_pointer_bound {T : Type} (id : Nat) (a : Allocation T)
    (start : Nat) (hstart : start ≤ a.cells.length) :
    (encodePointer (backedPointer id a start)).address.toNat =
      (backedPointer id a start).address ∧
    (backedPointer id a start).address < 2 ^ 64 := by
  have hn := a.noWrap
  have hs : a.base + start * 16 < 2 ^ 64 := by omega
  constructor
  · simp [encodePointer, backedPointer, BitVec.toNat_ofNat]
    exact hs
  · exact hs

theorem backed_pointer_decode {T : Type} (id : Nat) (a : Allocation T)
    (start : Nat) (hstart : start ≤ a.cells.length) :
    decodePointer (encodePointer (backedPointer id a start)) =
      backedPointer id a start := by
  apply decode_encode
  have hn := a.noWrap
  simp [backedPointer]
  omega

theorem word_index_fits {T : Type} (a : Allocation T)
    (index : Nat) (hindex : index < a.cells.length) :
    index < 2 ^ 64 := by
  have hs := a.small
  omega

theorem backed_word_offset_read_view {T : Type} (heap : Heap T)
    (id : Nat) (a : Allocation T) (hlookup : heap id = some a)
    (start length : Nat) (hbound : start + length ≤ a.cells.length)
    (index : Nat) (hindex : index < length) :
    ((offset heap (encodePointer (backedPointer id a start))
        (BitVec.ofNat 64 index)).bind
      (fun ptr => read heap (decodePointer ptr))) =
      some ((viewCells a start length).get
        ⟨index, by rw [view_length a start length hbound]; exact hindex⟩) := by
  have hs : start ≤ a.cells.length := by omega
  have hiCells : index < a.cells.length := by omega
  have hfit := word_index_fits a index hiCells
  have hcount : (BitVec.ofNat 64 index).toNat = index := by
    simp [BitVec.toNat_ofNat]
    exact hfit
  have hdecode := backed_pointer_decode id a start hs
  have hoff := offset_decode heap (encodePointer (backedPointer id a start))
    (BitVec.ofNat 64 index)
  rw [hcount, hdecode] at hoff
  calc
    ((offset heap (encodePointer (backedPointer id a start))
        (BitVec.ofNat 64 index)).bind
      (fun ptr => read heap (decodePointer ptr)))
        = (add heap (backedPointer id a start) index).bind (read heap) := by
            rw [← hoff]
            cases offset heap (encodePointer (backedPointer id a start)) (BitVec.ofNat 64 index) <;> rfl
    _ = some ((viewCells a start length).get
        ⟨index, by rw [view_length a start length hbound]; exact hindex⟩) :=
          read_view heap id a hlookup start length hbound index
            (by rw [view_length a start length hbound]; exact hindex)

#print axioms encodePointer
#print axioms decode_encode
#print axioms backed_pointer_bound
#print axioms backed_pointer_decode
#print axioms word_index_fits
#print axioms backed_word_offset_read_view
end AspisV8R19.R477BackedPointerWordImage
