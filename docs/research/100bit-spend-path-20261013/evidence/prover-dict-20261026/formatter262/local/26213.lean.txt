import R1Z.PDict_RowBits262
set_option autoImplicit false
namespace R1Z.PDict_RowTotal262
open Aeneas Aeneas.Std Result PDict_RowBits262
abbrev Variant := PDict_OwnedCell262.Variant

def srow (j : Usize) : Usize :=
  Usize.wrapping_shl (j &&& 3#usize) 6#u32 |||
  Usize.wrapping_shl (Usize.wrapping_shr j 2#u32 &&& 3#usize) 8#u32 |||
  Usize.wrapping_shl (Usize.wrapping_shr j 4#u32 &&& 3#usize) 4#u32 |||
  (Usize.wrapping_shr j 6#u32 &&& 3#usize) |||
  Usize.wrapping_shl (Usize.wrapping_shr j 8#u32 &&& 3#usize) 2#u32

theorem srow_bound (j : Usize) : (srow j).val < 1024 := by
  have a := shifted_digit_bound j 6#u32 (by scalar_tac)
  have b := shifted_digit_bound (Usize.wrapping_shr j 2#u32) 8#u32 (by scalar_tac)
  have c := shifted_digit_bound (Usize.wrapping_shr j 4#u32) 4#u32 (by scalar_tac)
  have d : (Usize.wrapping_shr j 6#u32 &&& 3#usize).val < 1024 :=
    (digit_bound _).trans (by decide)
  have e := shifted_digit_bound (Usize.wrapping_shr j 8#u32) 2#u32 (by scalar_tac)
  exact union_bound _ _ (union_bound _ _ (union_bound _ _ (union_bound _ _ a b) c) d) e

/-- The actual extracted row selector terminates and stays within the source
array for every variant and valid coordinate. D uses named table certificates. -/
theorem total (variant : Variant) (index : Usize) (small : index.val < 1024) :
    ∃ source : Usize, PDict_OwnedSource244.row.row variant index = .ok source ∧ source.val < 1024 := by
  cases variant with
  | S1 => exact ⟨srow index, rfl, srow_bound index⟩
  | S2 => exact ⟨srow index, rfl, srow_bound index⟩
  | D =>
    obtain ⟨value, read, bound⟩ := PDict_RowTable244.index_bound index small
    refine ⟨UScalar.cast .Usize value, ?_, ?_⟩
    · simp only [PDict_OwnedSource244.row.row, PDict_OwnedSource244.row.ORDER,
        read, bind_tc_ok]
    · rw [UScalar.cast_val_eq]
      exact lt_of_le_of_lt (Nat.mod_le _ _) bound

#print axioms srow
#print axioms srow_bound
#print axioms total
end R1Z.PDict_RowTotal262
