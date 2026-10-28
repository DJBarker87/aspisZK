import R1Z.PV_RDB2_NonNull

/-! Owned representation/effect laws for the other changed 1.94.1 NonNull
bodies. Absence of provenance is explicit and never treated as a valid
allocation. These constructors confer no permission to dereference. -/
namespace R1Z.PV_RDB2_ConstructorEffects
set_option autoImplicit false
open Aeneas Aeneas.Std Result

structure Raw where
  allocation : Option Nat
  address : Nat
  metadata : Option Nat

structure NonNull where
  pointer : Raw
  nonzero : pointer.address ≠ 0

def construct (p : Raw) (h : p.address ≠ 0) : NonNull := ⟨p,h⟩
def withoutProvenance (address : Nat) (h : address ≠ 0) : NonNull :=
  construct ⟨none,address,none⟩ h
def sliceFromRawParts (p : NonNull) (length : Nat) : NonNull :=
  construct {p.pointer with metadata := some length} p.nonzero

/-- `from_mut` only packages the reference pointer. The actual mutable write
and its restoration are obligations of the consuming callee, not this law. -/
theorem from_mut_complete {Heap Borrow : Type} (p : Raw) (h : p.address ≠ 0)
    (heap : Heap) (borrow : Borrow) :
    (ok (construct p h,heap,borrow) : Result (NonNull × Heap × Borrow)) =
      ok (⟨p,h⟩,heap,borrow) := rfl

/-- The unsafe precondition is checked on the admitted domain, whether or
not the distributed standard library enables its runtime UB assertion. -/
theorem new_unchecked_complete {Heap : Type} (p : Raw) (h : p.address ≠ 0)
    (heap : Heap) :
    (if p.address = 0 then fail .undef else ok (construct p h,heap)) =
      (ok (⟨p,h⟩,heap) : Result (NonNull × Heap)) := if_neg h

theorem without_provenance_complete {Heap : Type} (address : Nat)
    (h : address ≠ 0) (heap : Heap) :
    (ok ((withoutProvenance address h).pointer,heap) : Result (Raw × Heap)) =
      ok (⟨none,address,none⟩,heap) := rfl

theorem slice_complete {Heap Borrow : Type} (p : NonNull) (length : Nat)
    (heap : Heap) (borrow : Borrow) :
    (ok ((sliceFromRawParts p length).pointer,heap,borrow) : Result (Raw × Heap × Borrow)) =
      ok ({p.pointer with metadata := some length},heap,borrow) := rfl

theorem slice_nonzero (p : NonNull) (length : Nat) :
    (sliceFromRawParts p length).pointer.address ≠ 0 := p.nonzero

theorem slice_provenance (p : NonNull) (length : Nat) :
    (sliceFromRawParts p length).pointer.allocation = p.pointer.allocation := rfl

#print axioms from_mut_complete
#print axioms new_unchecked_complete
#print axioms without_provenance_complete
#print axioms slice_complete
#print axioms slice_nonzero
#print axioms slice_provenance
end R1Z.PV_RDB2_ConstructorEffects
