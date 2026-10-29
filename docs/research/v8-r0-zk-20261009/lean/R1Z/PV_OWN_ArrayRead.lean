import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem ArrayRead (k : Codec T) (c : Cell) (start i : Nat) (xs : List T) (x : T)
 (h:ArrayView k c start xs) (hi:xs[i]?=some x) : Represents k c (start+i*k.width) x := h.2 i x hi
#print axioms ArrayRead
end R1Z.PV_OWN_Laws
