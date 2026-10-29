import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem TruncateCapacity (v : Vector T) (n : Nat) : (truncate n v).capacity=v.capacity ∧
 (truncate n v).token=v.token ∧ (truncate n v).owner=v.owner := ⟨rfl,rfl,rfl⟩
#print axioms TruncateCapacity
end R1Z.PV_OWN_Laws
