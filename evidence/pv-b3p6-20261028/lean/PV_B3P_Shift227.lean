import Aeneas.Std
namespace PV_B3P_Shift227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem shift31_value : (31#i32).val = Int.ofNat (31#u32).val := rfl
theorem shift4_value : (4#i32).val = Int.ofNat (4#u32).val := rfl

theorem u8_u32_value (x : U8) : (UScalar.cast .U32 x).val = x.val := by
  simp only [UScalar.cast_val_eq]
  scalar_tac

#print axioms shift31_value
#print axioms shift4_value
#print axioms u8_u32_value
end PV_B3P_Shift227
