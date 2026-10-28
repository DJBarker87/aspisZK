import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem TruncateLength (v : Vector T) (n : Nat) : (truncate n v).values.length=min n v.values.length := by
 exact List.length_take
#print axioms TruncateLength
end R1Z.PV_OWN_Laws
