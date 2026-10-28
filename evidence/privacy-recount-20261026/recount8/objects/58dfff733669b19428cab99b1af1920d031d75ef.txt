import R1Z.PV_RDB2C_PV_B2_D_RowSource
import R1Z.PV_RDB2C_PV_B2_D_ShiftValue
import R1Z.PV_RDB2C_PV_B2_D_RawHelpersTotal
import R1Z.PV_RDB2C_PV_B2_C_TableRange
set_option autoImplicit false
namespace PV_B2_D_RowRange
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_D_RowSource
theorem digit0_bound (j : Usize) : (digit0 j).val < 1024 := by
  have hm := PV_B2_D_RawHelpersTotal.mask_bound (Usize.wrapping_shr j 0#u32)
  change (Usize.wrapping_shr j 0#u32 &&& 3#usize).val < 4 at hm
  unfold digit0
  rw [PV_B2_D_ShiftValue.shift_val _ _ (by decide)]
  rw [show (6#u32).val = 6 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit0_bound
theorem digit1_bound (j : Usize) : (digit1 j).val < 1024 := by
  have hm := PV_B2_D_RawHelpersTotal.mask_bound (Usize.wrapping_shr j 2#u32)
  change (Usize.wrapping_shr j 2#u32 &&& 3#usize).val < 4 at hm
  unfold digit1
  rw [PV_B2_D_ShiftValue.shift_val _ _ (by decide)]
  rw [show (8#u32).val = 8 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit1_bound
theorem digit2_bound (j : Usize) : (digit2 j).val < 1024 := by
  have hm := PV_B2_D_RawHelpersTotal.mask_bound (Usize.wrapping_shr j 4#u32)
  change (Usize.wrapping_shr j 4#u32 &&& 3#usize).val < 4 at hm
  unfold digit2
  rw [PV_B2_D_ShiftValue.shift_val _ _ (by decide)]
  rw [show (4#u32).val = 4 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit2_bound
theorem digit3_bound (j : Usize) : (digit3 j).val < 1024 := by
  have hm := PV_B2_D_RawHelpersTotal.mask_bound (Usize.wrapping_shr j 6#u32)
  change (Usize.wrapping_shr j 6#u32 &&& 3#usize).val < 4 at hm
  unfold digit3
  rw [PV_B2_D_ShiftValue.shift_val _ _ (by decide)]
  rw [show (0#u32).val = 0 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit3_bound
theorem digit4_bound (j : Usize) : (digit4 j).val < 1024 := by
  have hm := PV_B2_D_RawHelpersTotal.mask_bound (Usize.wrapping_shr j 8#u32)
  change (Usize.wrapping_shr j 8#u32 &&& 3#usize).val < 4 at hm
  unfold digit4
  rw [PV_B2_D_ShiftValue.shift_val _ _ (by decide)]
  rw [show (2#u32).val = 2 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit4_bound
theorem or_bound (a b : Usize) (ha : a.val < 1024) (hb : b.val < 1024) :
    (a ||| b).val < 1024 := by
  change (a ||| b).bv.toNat < 2^10
  rw [UScalar.bv_or,BitVec.toNat_or]
  exact Nat.or_lt_two_pow ha hb

theorem perm_bound (j : Usize) : (suffix0 j 0#usize).val < 1024 := by
  unfold suffix0 suffix1 suffix2 suffix3 suffix4 suffix5
  repeat' apply or_bound
  · decide
  · exact digit0_bound j
  · exact digit1_bound j
  · exact digit2_bound j
  · exact digit3_bound j
  · exact digit4_bound j

theorem D (j : Usize) (hj : j.val < (1024#usize).val) :
    ∃ r, host_weights.host_row .D j = ok r ∧ r.val < 1024 := by
  obtain ⟨x,hx,hr⟩ := PV_B2_C_TableRange.read_range j hj
  refine ⟨UScalar.cast .Usize x,?_,?_⟩
  · simp only [host_weights.host_row,host_weights.HOST_COEFFICIENT_TO_ROW,hx,bind_tc_ok]
  · simp only [UScalar.cast,UScalar.val,BitVec.zeroExtend_eq_setWidth,BitVec.toNat_setWidth]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hr

theorem source (v : transport.Variant) (j : Usize) (hj : j.val < (1024#usize).val) :
    ∃ r, host_weights.host_row v j = ok r ∧ r.val < 1024 := by
  cases v with
  | S1 => exact ⟨_,PV_B2_D_RowSource.S1 j,perm_bound j⟩
  | S2 => exact ⟨_,PV_B2_D_RowSource.S2 j,perm_bound j⟩
  | D => exact D j hj
#print axioms or_bound
#print axioms perm_bound
#print axioms D
#print axioms source
end PV_B2_D_RowRange
