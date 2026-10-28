import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem MoveDestination (m : Memory) (src dst : Nat) (t : Token) (c : Cell) (h:dst≠src) :
 (move src dst t c m).slots dst=some t := by simp [move,h]
#print axioms MoveDestination
end R1Z.PV_OWN_Laws
