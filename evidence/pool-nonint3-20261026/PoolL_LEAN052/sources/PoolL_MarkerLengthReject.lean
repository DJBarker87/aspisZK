import PoolL_MarkerLengthFacts
set_option autoImplicit false
namespace AspisR1.PoolL_MarkerLengthReject
open Aeneas Aeneas.Std Result PoolL_MarkerLengthSource

theorem occupied (bytes : Slice U8)
    (cp : bytes.val.length = 192 ∨ bytes.val.length = 1768) :
    PoolL_marker_length bytes = ok (.Err (.Custom 1095966757#u32)) := by
  rw [PoolL_MarkerLengthFacts.exact]
  have h : bytes.val.length ≠ (208#usize).val := by rcases cp with h | h <;> simp [h]
  simp [h]
#print axioms occupied
end AspisR1.PoolL_MarkerLengthReject
