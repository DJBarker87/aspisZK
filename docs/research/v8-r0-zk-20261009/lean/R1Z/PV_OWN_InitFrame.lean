import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem InitFrame (k : Codec T) (t : Token) (c : Cell) (s a : Nat) (v : T) (m : Memory)
 (h:a≠t.address) : (writeTyped k t c s v m).heap a=m.heap a := put_other _ _ _ _ h
#print axioms InitFrame
end R1Z.PV_OWN_Laws
