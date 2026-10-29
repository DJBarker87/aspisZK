import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem MoveOwnership (m : Memory) (src dst : Nat) (t : Token) (c : Cell)
 (h:Owned m src t c) (hd:dst≠src) :
 Owned (move src dst t c m) dst t {c with owner := dst} := by
 refine ⟨⟨put_same _ _ _,h.1.2.1,h.1.2.2⟩,?_,rfl⟩
 simp [move,hd]
#print axioms MoveOwnership
end R1Z.PV_OWN_Laws
