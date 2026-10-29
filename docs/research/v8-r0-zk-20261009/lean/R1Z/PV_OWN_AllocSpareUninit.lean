import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem AllocSpareUninit (r : Request) (owner i : Nat) : (emptyCell r.size r.alignment owner).contents i=none := rfl
#print axioms AllocSpareUninit
end R1Z.PV_OWN_Laws
