import R1Z.PDict_CopySource244
set_option autoImplicit false
namespace R1Z.PDict_Advance244
open Aeneas Aeneas.Std

/-- The extracted release addition is wrapping, but the symbolic loop guard
puts it strictly below overflow. No concrete1024-step reduction is needed. -/
theorem value (index : Usize) (small : index.val < 1024) :
    (Usize.wrapping_add index 1#usize).val = index.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  have one : (1#usize).val = 1 := by scalar_tac
  rw [one]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with bits | bits <;>
    simp only [UScalar.size, UScalarTy.Usize_numBits_eq, bits] <;> omega

#print axioms value
end R1Z.PDict_Advance244
