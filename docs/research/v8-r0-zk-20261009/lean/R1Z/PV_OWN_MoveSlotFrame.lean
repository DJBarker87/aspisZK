import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem MoveSlotFrame (m : Memory) (src dst i : Nat) (t : Token) (c : Cell) (hs:i≠src) (hd:i≠dst) :
 (move src dst t c m).slots i=m.slots i := by simp [move,hs,hd]
#print axioms MoveSlotFrame
end R1Z.PV_OWN_Laws
