import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem MoveRepresentation (k : Codec T) (c : Cell) (dst s : Nat) (v : T)
 (h:Represents k c s v) : Represents k {c with owner := dst} s v := h
#print axioms MoveRepresentation
end R1Z.PV_OWN_Laws
