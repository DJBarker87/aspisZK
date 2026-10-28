import R1Z.PV_RDB2C_Base_Pointer

/-! Operational representation transport for the reached 1.94.1 NonNull
constructors. `Representation` includes fat-pointer metadata. A sized-target
cast drops metadata but retains both address and allocation identity. The
source checker establishes the transparent single-field representation and
exact bodies. This does not give arbitrary integers pointer provenance. -/
namespace R1Z.PV_RDB2_NonNull
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_RDB2_Pointer

structure Representation where
  data : Pointer
  metadata : Option Nat

structure Wrapped where
  pointer : Representation

/-- Interpretation of the old transparent pointer-to-wrapper transmute. -/
def historicalPack (p : Representation) : Wrapped := ⟨p⟩
/-- Interpretation of the deployed explicit pointer-field construction. -/
def deployedPack (p : Representation) : Wrapped := {pointer := p}

def sized (p : Representation) : Representation := ⟨p.data,none⟩
def historicalCast (p : Wrapped) : Wrapped := historicalPack (sized p.pointer)
def deployedCast (p : Wrapped) : Wrapped := deployedPack (sized p.pointer)

theorem from_ref_complete {Heap Borrow : Type} (p : Representation)
    (heap : Heap) (borrow : Borrow) :
    (ok (deployedPack p,heap,borrow) : Result (Wrapped × Heap × Borrow)) =
      ok (historicalPack p,heap,borrow) := rfl

theorem cast_complete {Heap Borrow : Type} (p : Wrapped)
    (heap : Heap) (borrow : Borrow) :
    (ok (deployedCast p,heap,borrow) : Result (Wrapped × Heap × Borrow)) =
      ok (historicalCast p,heap,borrow) := rfl

theorem cast_provenance (p : Wrapped) :
    (deployedCast p).pointer.data = p.pointer.data := rfl

theorem cast_metadata (p : Wrapped) :
    (deployedCast p).pointer.metadata = none := rfl

theorem iterator_constructor (p : Pointer) (length : Nat) :
    (deployedCast (deployedPack ⟨p,some length⟩)).pointer = ⟨p,none⟩ := rfl

theorem nonnull_preserved (p : Wrapped) (h : p.pointer.data.address ≠ 0) :
    (deployedCast p).pointer.data.address ≠ 0 := h

#print axioms from_ref_complete
#print axioms cast_complete
#print axioms cast_provenance
#print axioms cast_metadata
#print axioms iterator_constructor
#print axioms nonnull_preserved
end R1Z.PV_RDB2_NonNull
