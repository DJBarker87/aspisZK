import R1Z.PV_OWND_PushCompose
set_option autoImplicit false
namespace R1Z.PV_OWND_PaddedFold
open PV_OWNC_Vector PV_OWN_View PV_OWN_Bytes
/-- Each source write can carry different padding, including initialized
padding. Only active representation bytes are constrained by its typed value. -/
def append {T : Type} (k : Codec T) : Buffer T → List T → (Nat → T → Bytes) → Nat → Buffer T
 | b,[],_,_ => b
 | b,v::vs,payload,j => append k (push k b v (payload j v)) vs payload (j+1)
attribute [local irreducible] append
end R1Z.PV_OWND_PaddedFold
