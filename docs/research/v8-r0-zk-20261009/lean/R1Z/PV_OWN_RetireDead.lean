import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem RetireDead (m : Memory) (t : Token) (c : Cell) :
 (retire t c m).heap t.address=some {c with live := false} := put_same _ _ _
#print axioms RetireDead
end R1Z.PV_OWN_Laws
