import R1Z.PV_CBL_ByteStoreValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteStoreCoordinate
set_option autoImplicit false
theorem byte (w : U32) (j : Nat) (hj : j<4) :
    (PV_CBL_ByteCodecValue.store w).val[j]! = PV_CBL_ByteStoreValue.byte w j := by
  have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases h with rfl|rfl|rfl|rfl <;> rfl
#print axioms byte
end R1Z.PV_CBL_ByteStoreCoordinate
