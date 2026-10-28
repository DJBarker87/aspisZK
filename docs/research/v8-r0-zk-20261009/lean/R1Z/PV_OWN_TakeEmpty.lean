import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem TakeEmpty (m : Memory) (s : Nat) : (take s m).slots s=none := by simp [take]
#print axioms TakeEmpty
end R1Z.PV_OWN_Laws
