import NHY_ZeroStep
set_option autoImplicit false
namespace NIJ_CheckpointAdvance
open Aeneas Aeneas.Std Result

theorem value (i : Usize) (bound : i.val < 1768) :
 (i.wrapping_add 1#usize).val=i.val+1 := by
 -- Minimal retarget of FGm_UsizeNext.val: its historical object is absent;
 -- importing its field-array cone would rebuild unrelated modules.
 rw [Usize.wrapping_add_val_eq]
 change (i.val+1)%UScalar.size .Usize=i.val+1
 apply Nat.mod_eq_of_lt
 apply lt_of_le_of_lt (show i.val+1≤(1768#usize).val from by scalar_tac)
 simpa only [UScalar.size,UScalar.val,UScalarTy.numBits] using (1768#usize).bv.isLt


#print axioms value
end NIJ_CheckpointAdvance
