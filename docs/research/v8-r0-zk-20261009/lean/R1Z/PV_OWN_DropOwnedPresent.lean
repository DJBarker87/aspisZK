import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem DropOwnedPresent (slot : Nat) (glue : Token → Action S X E Unit) (w : State S X) (t : Token)
 (h:w.memory.slots slot=some t) :
 dropOwned slot glue w=glue t {w with memory := take slot w.memory} := by simp [dropOwned,h]
#print axioms DropOwnedPresent
end R1Z.PV_OWN_Laws
