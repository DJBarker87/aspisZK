import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem SequenceDivergence (a : Action S X E Unit) (rest : List (Action S X E Unit)) (w : State S X)
 (h:(a w).outcome=.div) :
 sequence (a::rest) w=⟨.div,(a w).world,(a w).calls⟩ := bind_div a _ w h
#print axioms SequenceDivergence
end R1Z.PV_OWN_Laws
