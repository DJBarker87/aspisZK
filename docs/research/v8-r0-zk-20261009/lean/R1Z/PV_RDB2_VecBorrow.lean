import R1Z.PV_RDB2_CopyEffects

/-! The slice borrow exposes initialized elements only. Restoration retains
all returned element writes, capacity, allocator identity and spare cells.
This models the Copy-element Vec families consumed by these rows. -/
namespace R1Z.PV_RDB2_VecBorrow
set_option autoImplicit false
open Aeneas Aeneas.Std Result

structure VecState (T Allocator : Type) where
  initialized : List T
  spare : List (Option T)
  capacity : Nat
  allocator : Allocator
  exact_capacity : initialized.length+spare.length=capacity

def restore {T Allocator : Type} (before : VecState T Allocator) (changed : List T)
    (length : changed.length = before.initialized.length) : VecState T Allocator :=
  {initialized := changed,spare := before.spare,capacity := before.capacity,
   allocator := before.allocator,exact_capacity := by rw [length];exact before.exact_capacity}

def borrow {T Allocator : Type} (before : VecState T Allocator) : List T := before.initialized

theorem complete_return {T Allocator : Type} (before : VecState T Allocator) (changed : List T)
    (length : changed.length = before.initialized.length) :
    (restore before changed length).initialized = changed ∧
      (restore before changed length).spare = before.spare ∧
      (restore before changed length).capacity = before.capacity ∧
      (restore before changed length).allocator = before.allocator := ⟨rfl,rfl,rfl,rfl⟩

theorem every_write {T Allocator : Type} (before : VecState T Allocator) (changed : List T)
    (length : changed.length = before.initialized.length) (i : Nat) :
    (restore before changed length).initialized[i]? = changed[i]? := rfl

theorem roundtrip {T Allocator : Type} (before : VecState T Allocator) :
    restore before (borrow before) rfl = before := by cases before; rfl

theorem no_spare_exposure {T Allocator : Type} (before : VecState T Allocator) :
    (borrow before).length = before.initialized.length ∧
      (borrow before).length ≤ before.capacity := by
  exact ⟨rfl,by have := before.exact_capacity; unfold borrow; omega⟩

theorem initialized_read {T Allocator : Type} (before : VecState T Allocator)
    (i : Nat) (h : i < (borrow before).length) :
    (borrow before)[i]? = some before.initialized[i] := by
  exact List.getElem?_eq_getElem h

#print axioms complete_return
#print axioms every_write
#print axioms roundtrip
#print axioms no_spare_exposure
#print axioms initialized_read
end R1Z.PV_RDB2_VecBorrow
