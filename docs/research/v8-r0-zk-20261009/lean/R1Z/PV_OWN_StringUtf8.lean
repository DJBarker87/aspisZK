import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem StringUtf8 (k : Codec UInt8) (utf8 : List UInt8 → Prop) (m : Memory) (v : Vector UInt8)
 (h:StringView k utf8 m v) : utf8 v.values := h.2
#print axioms StringUtf8
end R1Z.PV_OWN_Laws
