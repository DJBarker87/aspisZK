import Aeneas
set_option autoImplicit false
namespace PV_B1_Shift31
open Aeneas Aeneas.Std Result

theorem literal : (31#i32).val = ((31#u32).val : Int) := rfl

theorem nonfailure (x : U64) :
    (lift (U64.wrapping_shr x 31#u32) : Result U64) =
      ok (U64.wrapping_shr x 31#u32) := rfl

theorem value (x : U64) :
    (U64.wrapping_shr x 31#u32).val = x.val / 2^31 := by
  change (x.bv.ushiftRight (31 % 64)).toNat = _
  change x.val >>> 31 = x.val / 2^31
  rw [Nat.shiftRight_eq_div_pow]

#print axioms literal
#print axioms nonfailure
#print axioms value
end PV_B1_Shift31
