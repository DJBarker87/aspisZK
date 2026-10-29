import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem MoveLive (m : Memory) (src dst : Nat) (t : Token) (c : Cell) (h:Live m t c) :
 Live (move src dst t c m) t {c with owner := dst} := ⟨put_same _ _ _,h.2.1,h.2.2⟩
#print axioms MoveLive
end R1Z.PV_OWN_Laws
