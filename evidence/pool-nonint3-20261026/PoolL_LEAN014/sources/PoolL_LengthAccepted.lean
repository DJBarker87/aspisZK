import PoolL_LengthFacts
set_option autoImplicit false
namespace AspisR1.PoolL_LengthAccepted
open Aeneas Aeneas.Std Result PoolL_LengthSource

theorem accepted (data : Slice U8) (size : Usize) :
    lengthPrefix data size = ok (.Ok ()) ↔ data.val.length = size.val := by
  rw [PoolL_LengthFacts.exact]
  simp [Slice.len]

#print axioms accepted
end AspisR1.PoolL_LengthAccepted
