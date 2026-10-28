import Aeneas.Std
namespace PV_B3P_MaskCasts132
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem row (r : Usize) (hr : r.val < 1024) :
    (UScalar.cast .U16 r).val = r.val := by
  rw [UScalar.cast_val_eq]
  change r.val % 65536 = r.val
  omega

theorem column (c : Usize) (hc : c.val < 16) :
    (UScalar.cast .U8 c).val = c.val := by
  rw [UScalar.cast_val_eq]
  change c.val % 256 = c.val
  omega
#print axioms row
#print axioms column
end PV_B3P_MaskCasts132
