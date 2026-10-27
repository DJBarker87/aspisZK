import PoolL_FreshLengthFacts
import PoolL_LengthOccupied
set_option autoImplicit false
namespace AspisR1.PoolL_FreshLengthReject
open Aeneas Aeneas.Std Result PoolL_FreshLengthSource

theorem occupied (bytes : Slice U8) (size : Usize)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768)
    (other : PoolL_LengthOccupied.OtherWidth size.val) :
    PoolL_fresh_length bytes size = ok (.Err (.Custom 1095966773#u32)) := by
  rw [PoolL_FreshLengthFacts.exact]
  simp [PoolL_LengthOccupied.disjoint _ _ cp other]
#print axioms occupied
end AspisR1.PoolL_FreshLengthReject
