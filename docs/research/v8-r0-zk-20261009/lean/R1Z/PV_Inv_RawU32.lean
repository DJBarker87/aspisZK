import R1Z.PV_Inv_NativeQ
set_option autoImplicit false
namespace R1Z.PV_Inv_RawU32
open Aeneas Aeneas.Std
instance zeroU32 : Zero U32 := ⟨0#u32⟩
theorem zero_value : (0 : U32) = 0#u32 := rfl
#print axioms zero_value
end R1Z.PV_Inv_RawU32
