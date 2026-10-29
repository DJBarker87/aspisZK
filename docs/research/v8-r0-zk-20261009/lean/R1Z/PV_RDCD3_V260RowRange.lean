import R1Z.PV_RDCD3_V260RowSource
import R1Z.PV_B2_C_TableRange
set_option autoImplicit false
namespace R1Z.PV_RDCD3_V260RowRange
open Aeneas Aeneas.Std Result PV_B2_253c1 PV_RDCD3_V260RowSource
theorem mask_bound (x : Usize) : (x &&& 3#usize).val < (4#usize).val := by
  change (x &&& 3#usize).bv.toNat < 4
  rw [UScalar.bv_and,BitVec.toNat_and]
  exact lt_of_le_of_lt (Nat.and_le_right) (by decide)

theorem shift_val (x : Usize) (b : U32) (hb : b.val < 32) :
    (Usize.wrapping_shl x b).val = (x.val * 2^b.val) % UScalar.size .Usize := by
  unfold Usize.wrapping_shl UScalar.wrapping_shl
  simp only [UScalar.val,BitVec.shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,UScalar.size]
  have h : b.val < UScalarTy.Usize.numBits := lt_of_lt_of_le hb System.Platform.le_numBits
  have h1 : b.bv.toNat < UScalarTy.Usize.numBits := by simpa only [UScalar.val] using h
  rw [Nat.mod_eq_of_lt h1]
#print axioms mask_bound
#print axioms shift_val

theorem digit0_bound (j : Usize) : (digit0 j).val < 1024 := by
  have hm := mask_bound (Usize.wrapping_shr j 0#u32)
  change (Usize.wrapping_shr j 0#u32 &&& 3#usize).val < 4 at hm
  unfold digit0
  rw [shift_val _ _ (by decide)]
  rw [show (6#u32).val = 6 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit0_bound
theorem digit1_bound (j : Usize) : (digit1 j).val < 1024 := by
  have hm := mask_bound (Usize.wrapping_shr j 2#u32)
  change (Usize.wrapping_shr j 2#u32 &&& 3#usize).val < 4 at hm
  unfold digit1
  rw [shift_val _ _ (by decide)]
  rw [show (8#u32).val = 8 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit1_bound
theorem digit2_bound (j : Usize) : (digit2 j).val < 1024 := by
  have hm := mask_bound (Usize.wrapping_shr j 4#u32)
  change (Usize.wrapping_shr j 4#u32 &&& 3#usize).val < 4 at hm
  unfold digit2
  rw [shift_val _ _ (by decide)]
  rw [show (4#u32).val = 4 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit2_bound
theorem digit3_bound (j : Usize) : (digit3 j).val < 1024 := by
  have hm := mask_bound (Usize.wrapping_shr j 6#u32)
  change (Usize.wrapping_shr j 6#u32 &&& 3#usize).val < 4 at hm
  unfold digit3
  rw [shift_val _ _ (by decide)]
  rw [show (0#u32).val = 0 from rfl]
  apply lt_of_le_of_lt (Nat.mod_le _ _)
  norm_num only [Nat.reducePow]
  omega
#print axioms digit3_bound
theorem digit4_bound (j : Usize) : (digit4 j).val < 1024 := by
  have hm := mask_bound (Usize.wrapping_shr j 8#u32)
  change (Usize.wrapping_shr j 8#u32 &&& 3#usize).val < 4 at hm
  unfold digit4
  rw [shift_val _ _ (by decide)]
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
  | S1 => exact ⟨_,PV_RDCD3_V260RowSource.S1 j,perm_bound j⟩
  | S2 => exact ⟨_,PV_RDCD3_V260RowSource.S2 j,perm_bound j⟩
  | D => exact D j hj
#print axioms or_bound
#print axioms perm_bound
#print axioms D
#print axioms source
end R1Z.PV_RDCD3_V260RowRange
