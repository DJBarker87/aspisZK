import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem MoveHeapFrame (m : Memory) (src dst p : Nat) (t : Token) (c : Cell) (h:p≠t.address) :
 (move src dst t c m).heap p=m.heap p := put_other _ _ _ _ h
#print axioms MoveHeapFrame
end R1Z.PV_OWN_Laws
