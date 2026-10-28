import Aeneas.Std
namespace PV_B3P_HelperShiftPrefix224
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem amount (level : U8) : (UScalar.cast .U32 level).val = level.val := by
  rw [UScalar.cast_val_eq]
  change level.val % 4294967296 = level.val
  have h : level.val < 256 := by scalar_tac
  omega
#print axioms amount
end PV_B3P_HelperShiftPrefix224
