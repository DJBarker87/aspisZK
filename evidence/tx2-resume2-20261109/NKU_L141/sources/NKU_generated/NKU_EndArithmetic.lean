import NKU_HeaderDomain
set_option autoImplicit false
namespace NKU_EndArithmetic
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem wrap : Std.Usize.wrapping_sub 1768#usize 32#usize=1736#usize := by
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_sub_val_eq]
 have bound : 1768<UScalar.size .Usize := by scalar_tac
 change (1768+(UScalar.size .Usize-32))%UScalar.size .Usize=1736
 rw [show 1768+(UScalar.size .Usize-32)=1736+UScalar.size .Usize by omega,
  Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
#print axioms wrap
end NKU_EndArithmetic
