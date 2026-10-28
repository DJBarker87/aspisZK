import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem RetireBytes (c : Cell) : ({c with live := false} : Cell).contents=c.contents ∧
 ({c with live := false} : Cell).size=c.size ∧
 ({c with live := false} : Cell).alignment=c.alignment := ⟨rfl,rfl,rfl⟩
#print axioms RetireBytes
end R1Z.PV_OWN_Laws
