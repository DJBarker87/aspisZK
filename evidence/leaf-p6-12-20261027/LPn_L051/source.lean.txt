import LPn_ByteBound
import LPn_Kit_ByteFields
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace LPn.Bytes

theorem word_val (bs : List U8) : (LPn_Kit_word bs).val = LPl_Kit_Bytes.le32 bs := by
  change LPl_Kit_Bytes.le32 bs % 4294967296 = LPl_Kit_Bytes.le32 bs
  exact Nat.mod_eq_of_lt (le32_bound bs)

theorem word_canonical_iff (bs : List U8) :
    LPn_Kit_word bs < 2147483647#u32 ↔ LPl_Kit_Bytes.le32 bs < 2147483647 := by
  change (LPn_Kit_word bs).val < 2147483647 ↔ _
  rw [word_val]

#print axioms word_val
#print axioms word_canonical_iff
end LPn.Bytes
