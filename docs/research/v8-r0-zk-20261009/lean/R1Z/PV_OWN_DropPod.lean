import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem DropPod (w : State S X) : (dropPod (E:=E) w).outcome=.ok () ∧
 (dropPod (E:=E) w).world=w ∧ (dropPod (E:=E) w).calls=[] := ⟨rfl,rfl,rfl⟩
#print axioms DropPod
end R1Z.PV_OWN_Laws
