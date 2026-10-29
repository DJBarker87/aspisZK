import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem RetireNoLive (m : Memory) (t : Token) (c d : Cell) : ¬Live (retire t c m) t d := by
 intro h
 have eq:{c with live := false}=d := Option.some.inj ((put_same _ _ _).symm.trans h.1)
 subst d
 cases h.2.1
#print axioms RetireNoLive
end R1Z.PV_OWN_Laws
