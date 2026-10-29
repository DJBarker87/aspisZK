import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem SequenceFailure (a : Action S X E Unit) (rest : List (Action S X E Unit)) (w : State S X)
 (e : E) (h:(a w).outcome=.fail e) :
 sequence (a::rest) w=⟨.fail e,(a w).world,(a w).calls⟩ := bind_fail a _ w e h
#print axioms SequenceFailure
end R1Z.PV_OWN_Laws
