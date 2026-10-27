import R1Z.PV_CBL_StringCapacityBytes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_CapacityValue
set_option autoImplicit false
/-- The representation adapter accepts only the empty byte value. -/
def decodeEmpty (v : alloc.vec.Vec U8) : Result String :=
  if v.val = [] then ok "" else fail .panic
def reference (n : Usize) : Result String := do
  let v ← PV_CBL_StringCapacityBytes.string_capacity_bytes_reference n
  decodeEmpty v
theorem bytes (n : Usize) :
    PV_CBL_StringCapacityBytes.string_capacity_bytes_reference n =
      ok (alloc.vec.Vec.new U8) := rfl
theorem value (n : Usize) : reference n = ok "" := by
  simp [reference,PV_CBL_StringCapacityBytes.string_capacity_bytes_reference,
    decodeEmpty,alloc.vec.Vec.new,bind_tc_ok]
#print axioms decodeEmpty
#print axioms reference
#print axioms bytes
#print axioms value
end R1Z.PV_CBL_CapacityValue
