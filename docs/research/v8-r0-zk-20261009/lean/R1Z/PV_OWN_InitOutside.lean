import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem InitOutside (k : Codec T) (t : Token) (c : Cell) (s i : Nat) (v : T) (m : Memory)
 (h:i<s ∨ s+k.width≤i) :
 (store c s k.width (k.encode v)).contents i=c.contents i := outside _ _ _ _ _ h
#print axioms InitOutside
end R1Z.PV_OWN_Laws
