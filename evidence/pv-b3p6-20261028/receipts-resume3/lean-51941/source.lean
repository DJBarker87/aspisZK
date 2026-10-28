import Aeneas.Std
namespace PV_B3P_Shift224
open Aeneas Aeneas.Std
set_option autoImplicit false
-- The backend's unsigned wrapping-shift API expects a U32 amount. Both
-- source-typed positive literals denote the same nonnegative integer.
theorem shift31_value : (31#i32).val = Int.ofNat (31#u32).val := rfl
#print axioms shift31_value
end PV_B3P_Shift224
