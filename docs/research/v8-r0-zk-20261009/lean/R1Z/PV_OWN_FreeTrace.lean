import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem FreeTrace (prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) (w : State S X) :
 (free prim t c w).calls=[(w,.deallocate t.address c.size c.alignment)] := rfl
#print axioms FreeTrace
end R1Z.PV_OWN_Laws
