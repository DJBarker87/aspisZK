import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem DropString (prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) :
 dropString (X:=X) prim t c=dropVecPod prim t c := rfl
#print axioms DropString
end R1Z.PV_OWN_Laws
