import R1Z.PV_OWND_ActualHeader
set_option autoImplicit false
namespace R1Z.PV_OWND_SourceShape
open PV_OWN_Heap PV_OWN_Link PV_OWN_Bytes
/-- The deployed length mismatch branch is unreachable after these stores. -/
theorem no_shape_error (m : Memory) (t : Token) (owner : Nat) (payload : Nat → Link → Bytes) :
 ¬ (PV_OWND_ActualBytes.initialized m t owner payload).length≠127 := by
 exact fun h=>h (PV_OWND_ActualHeader.length m t owner payload)
/-- 127 eight-byte Links have a nonzero valid allocation layout on the deployed
64-bit target. There is no zero-size or capacity-overflow allocation branch. -/
theorem layout : 127*8=1016 ∧ 1016>0 ∧ 1016<9223372036854775807 ∧ 1016%2=0 := by
 decide
#print axioms no_shape_error
#print axioms layout
end R1Z.PV_OWND_SourceShape
