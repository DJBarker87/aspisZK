import FGm_ArrayUpdate
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGm_UsizeNext
open Aeneas Aeneas.Std Result

theorem val (i N : Usize) (hi : i<N) :
    (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  apply lt_of_le_of_lt (show i.val+1≤N.val from by scalar_tac)
  simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using N.bv.isLt

#print axioms val
end AspisR1.FGm_UsizeNext
end
