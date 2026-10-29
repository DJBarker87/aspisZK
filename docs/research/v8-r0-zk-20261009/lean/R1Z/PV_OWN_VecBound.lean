import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem VecBound (k : Codec T) (m : Memory) (v : Vector T) (h:VecView k m v) :
 v.values.length≤v.capacity := h.choose_spec.2.2.2.1
#print axioms VecBound
end R1Z.PV_OWN_Laws
