import AspisV8R19.R432PointerPrimitive

/-! NonNull validity in the explicit R432 allocation fragment. The conversion
checks the nonzero address and retains the complete pointer, including origin.
These are prerequisite facts for the live R440 Fun70 transmute, not a proof of
Rust/LLBC cast semantics or of the actual slice input's validity. -/
set_option autoImplicit false
namespace AspisV8R19.R471NonNullPointerValidity
open AspisV8R19.R432PointerPrimitive

structure NonNullPointer where
  pointer : Pointer
  valid : 0 < pointer.address

def wrap (ptr : Pointer) : Option NonNullPointer :=
  if h : 0 < ptr.address then some ⟨ptr, h⟩ else none

def unwrap (ptr : NonNullPointer) : Pointer := ptr.pointer

theorem wrap_success_iff (ptr : Pointer) :
    (∃ result, wrap ptr = some result) ↔ 0 < ptr.address := by
  simp only [wrap]
  split <;> simp_all

theorem wrap_exact (ptr : Pointer) (h : 0 < ptr.address) :
    wrap ptr = some ⟨ptr, h⟩ := by simp [wrap, h]

theorem wrap_unwrap (ptr : NonNullPointer) :
    wrap (unwrap ptr) = some ptr := by
  cases ptr with
  | mk pointer valid => exact wrap_exact pointer valid

theorem unwrap_wrap (ptr : Pointer) (h : 0 < ptr.address) :
    (wrap ptr).map unwrap = some ptr := by
  rw [wrap_exact ptr h]
  rfl

theorem wrap_preserves_pointer (ptr : Pointer) (result : NonNullPointer)
    (h : wrap ptr = some result) : unwrap result = ptr := by
  unfold wrap at h
  split at h
  · cases h
    rfl
  · contradiction

theorem wrap_preserves_origin (ptr : Pointer) (result : NonNullPointer)
    (h : wrap ptr = some result) : (unwrap result).origin = ptr.origin := by
  rw [wrap_preserves_pointer ptr result h]

theorem wrap_null (origin : Option (Nat × Nat)) :
    wrap ⟨0, origin⟩ = none := by simp [wrap]

theorem add_address_mono {T : Type} (heap : Heap T)
    (ptr last : Pointer) (count : Nat) (h : add heap ptr count = some last) :
    ptr.address ≤ last.address := by
  unfold add at h
  split at h
  · cases h
    exact Nat.le_refl _
  · cases ho : ptr.origin with
    | none => simp [ho] at h
    | some origin =>
      rcases origin with ⟨id, offset⟩
      cases ha : heap id with
      | none => simp [ho, ha] at h
      | some a =>
        simp [ho, ha] at h
        rcases h with ⟨_, _, he⟩
        rw [← he]
        simp only
        omega

theorem add_preserves_nonzero {T : Type} (heap : Heap T)
    (ptr last : Pointer) (count : Nat) (hptr : 0 < ptr.address)
    (h : add heap ptr count = some last) : 0 < last.address := by
  have hm := add_address_mono heap ptr last count h
  omega

theorem iterator_endpoints_valid {T : Type} (heap : Heap T)
    (ptr : Pointer) (length : Nat) (iter : Iter) (hptr : 0 < ptr.address)
    (h : newIter heap ptr length = some iter) :
    0 < iter.first.address ∧ 0 < iter.last.address := by
  unfold newIter at h
  cases ha : add heap ptr length with
  | none => simp [ha] at h
  | some last =>
    simp [ha] at h
    cases h
    exact ⟨hptr, add_preserves_nonzero heap ptr last length hptr ha⟩

theorem iterator_casts_total {T : Type} (heap : Heap T)
    (ptr : Pointer) (length : Nat) (iter : Iter) (hptr : 0 < ptr.address)
    (h : newIter heap ptr length = some iter) :
    (wrap iter.first).map unwrap = some iter.first ∧
    (wrap iter.last).map unwrap = some iter.last := by
  have hv := iterator_endpoints_valid heap ptr length iter hptr h
  exact ⟨unwrap_wrap _ hv.1, unwrap_wrap _ hv.2⟩

-- Empty slices may have no allocation/provenance. Nonzero dangling pointers
-- still convert; a zero pointer is rejected even when the slice is empty.
theorem empty_dangling_cast {T : Type} (heap : Heap T) (address : Nat)
    (haddress : 0 < address) :
    newIter heap ⟨address, none⟩ 0 = some ⟨⟨address, none⟩, ⟨address, none⟩⟩ ∧
    (wrap ⟨address, none⟩).map unwrap = some ⟨address, none⟩ := by
  exact ⟨newIter_empty heap _, unwrap_wrap _ haddress⟩

theorem backed_endpoint_cast {T : Type} (id : Nat) (a : Allocation T)
    (index : Nat) :
    (wrap (backedPointer id a index)).map unwrap =
      some (backedPointer id a index) := by
  apply unwrap_wrap
  have h := a.nonzero
  simp only [backedPointer]
  omega

#print axioms wrap_success_iff
#print axioms wrap_exact
#print axioms wrap_unwrap
#print axioms unwrap_wrap
#print axioms wrap_preserves_pointer
#print axioms wrap_preserves_origin
#print axioms wrap_null
#print axioms add_address_mono
#print axioms add_preserves_nonzero
#print axioms iterator_endpoints_valid
#print axioms iterator_casts_total
#print axioms empty_dangling_cast
#print axioms backed_endpoint_cast
end AspisV8R19.R471NonNullPointerValidity
