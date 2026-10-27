import LPa_ByteBound
import XRk_ByteFields
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace LPa.Bytes

theorem word_val (bs : List U8) : (XRk_word bs).val = XRk_Bytes.le32 bs := by
  change XRk_Bytes.le32 bs % 4294967296 = XRk_Bytes.le32 bs
  exact Nat.mod_eq_of_lt (le32_bound bs)

theorem word_canonical_iff (bs : List U8) :
    XRk_word bs < 2147483647#u32 ↔ XRk_Bytes.le32 bs < 2147483647 := by
  change (XRk_word bs).val < 2147483647 ↔ _
  rw [word_val]

#print axioms word_val
#print axioms word_canonical_iff
end LPa.Bytes
