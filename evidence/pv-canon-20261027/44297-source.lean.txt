import R1Z.PV_Canon_Carrier
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std
 theorem legacy_mask_canonical (word : U32)
    (accepted : word &&& 2147483647#u32 ≠ 2147483647#u32) :
    M (word &&& 2147483647#u32) := by
  unfold M
  have bound : (word &&& 2147483647#u32).val ≤ 2147483647 := by
    rw [U32.and_val_eq]
    exact Nat.and_le_right _ _
  have ne : (word &&& 2147483647#u32).val ≠ 2147483647 := by
    intro h
    apply accepted
    apply UScalar.eq_of_val_eq
    exact h
  omega
#print axioms legacy_mask_canonical
end R1Z.PV_Canon
