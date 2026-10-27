import LPa_CanonicalAdd
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace LPa.Add
-- Independent u64/Nat reference formula used by native K020.
theorem word_val_canonical (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    (word a b).val = if 2147483647 ≤ a.val+b.val
      then a.val+b.val-2147483647 else a.val+b.val := by
  have nowrap : a.val+b.val < 4294967296 := by omega
  have sum : (U32.wrapping_add a b).val = a.val+b.val := by scalar_tac
  unfold word
  split <;> scalar_tac
#print axioms word_val_canonical
end LPa.Add
