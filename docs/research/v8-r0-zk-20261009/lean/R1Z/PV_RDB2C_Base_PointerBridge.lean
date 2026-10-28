import R1Z.PV_RDB2C_Base_ConstructorEffects

/-! Connect the live-allocation pointer used by the cursor proof to the
explicit optional-provenance constructor model. A no-provenance pointer is
never decoded into a live cursor by this bridge. -/
namespace R1Z.PV_RDB2_PointerBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result

def encode (p : PV_RDB2_Pointer.Pointer) (metadata : Option Nat) :
    PV_RDB2_ConstructorEffects.Raw := ⟨some p.allocation,p.address,metadata⟩

def wrapped (p : PV_RDB2_NonNull.Wrapped) : PV_RDB2_ConstructorEffects.Raw :=
  encode p.pointer.data p.pointer.metadata

theorem cast_complete (p : PV_RDB2_NonNull.Wrapped) :
    wrapped (PV_RDB2_NonNull.deployedCast p) = {wrapped p with metadata := none} := rfl

theorem constructor_complete {World Borrow : Type} (p : PV_RDB2_Pointer.Pointer)
    (metadata : Option Nat) (nonzero : p.address ≠ 0) (world : World) (borrow : Borrow) :
    (ok ((PV_RDB2_ConstructorEffects.construct (encode p metadata) nonzero).pointer,world,borrow) :
      Result (PV_RDB2_ConstructorEffects.Raw × World × Borrow)) =
      ok (encode p metadata,world,borrow) := rfl

theorem slice_complete (p : PV_RDB2_Pointer.Pointer) (nonzero : p.address ≠ 0) (n : Nat) :
    (PV_RDB2_ConstructorEffects.sliceFromRawParts
      (PV_RDB2_ConstructorEffects.construct (encode p none) nonzero) n).pointer =
      encode p (some n) := rfl

theorem live_provenance (p : PV_RDB2_Pointer.Pointer) (metadata : Option Nat) :
    (encode p metadata).allocation = some p.allocation := rfl

#print axioms cast_complete
#print axioms constructor_complete
#print axioms slice_complete
#print axioms live_provenance
end R1Z.PV_RDB2_PointerBridge
