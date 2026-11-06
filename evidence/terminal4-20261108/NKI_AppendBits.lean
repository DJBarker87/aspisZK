import NKI_AppendPacket
import RPv_FIy_FrontierMeaning
set_option autoImplicit false
namespace AspisR1.NKI_AppendBits
open Aeneas Aeneas.Std
/-- Link the Rust shift/and branch to the adopted frontier predicate. No
assumption on index bits or honest index value is introduced. -/
theorem source (index : U64) (level : Usize) :
 NKI_AppendPacket.emptySide index level=decide (((index.val >>> level.val) &&& 1)=0) := by
 unfold NKI_AppendPacket.emptySide
 rw [Nat.and_two_pow_sub_one_eq_mod (index.val >>> level.val) 1]
 rw [Nat.shiftRight_eq_div_pow]
#print axioms source
end AspisR1.NKI_AppendBits
