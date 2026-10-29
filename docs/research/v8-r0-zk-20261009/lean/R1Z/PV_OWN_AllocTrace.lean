import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem AllocTrace (prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (owner : Nat)
 (w : State S X) : (allocate prim r owner w).calls=[(w,.allocate r.size r.alignment)] := rfl
#print axioms AllocTrace
end R1Z.PV_OWN_Laws
