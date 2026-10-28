import R1Z.PV_B2_D_ScalarCanonical
import R1Z.PV_B2_E_OrdinaryOriginal
set_option autoImplicit false
namespace PV_B2_E_CtDecoder
open Aeneas Aeneas.Std PV_B2_D_ReducerBounds

theorem fold_small (x : BitVec 64) (h : x.toNat < 2147483647) : fold64 x = x := by
  apply BitVec.eq_of_toNat_eq
  rw [fold_val]
  have h31 : x.toNat < 2147483648 := by omega
  have h64 : x.toNat < 18446744073709551616 := x.isLt
  rw [Nat.mod_eq_of_lt h31,Nat.div_eq_of_lt h31,Nat.add_zero,Nat.mod_eq_of_lt h64]

theorem reduced_small (x : BitVec 64) (h : x.toNat < 2147483647) :
    reduced x = x.setWidth 32 := by
  have hw : word x = x.setWidth 32 := by
    unfold word
    rw [fold_small x h,fold_small x h]
  have hn : (word x).toNat < 2147483647 := by
    rw [hw,BitVec.toNat_setWidth,Nat.mod_eq_of_lt (by omega)]
    exact h
  have hp : ¬ 2147483647 ≤ (word x).toNat := Nat.not_le_of_gt hn
  simp only [reduced,BitVec.ule,show (2147483647#32).toNat = 2147483647 from rfl,
    hp,decide_false,if_neg]
  change word x - 0#32 = x.setWidth 32
  simpa only [BitVec.sub_zero] using hw

/-- Exact source-shaped scalar expression, using the unchanged extracted ct body. -/
theorem source_shape (x : U64) :
    (PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64 x).val = (reduced x.bv).toNat := by
  unfold PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64
    PV_B2_C_251FieldValue.aspis_core.field.ct.subtract_p
    PV_B2_C_251FieldValue.aspis_core.field.P
  simp only [UScalar.lt_equiv,UScalar.le_equiv,UScalar.val,UScalar.cast,
    UScalar.cast_fromBool,UScalar.wrapping_shr,core.num.U32.wrapping_sub,
    U64.wrapping_add,U64.wrapping_shr,UScalar.wrapping_add,UScalar.wrapping_sub,
    UScalar.bv_and,UScalarTy.numBits,BitVec.zeroExtend_eq_setWidth,decide_eq_true_eq,
    U32.ofNat_bv]
  simp only [show BitVec.setWidth 64 2147483647#32 = 2147483647#64 from by decide,
    show (31#32).toNat % 64 = 31 from rfl,
    show (2147483647#32).toNat = 2147483647 from rfl]
  norm_num only [reduced,word,fold64,BitVec.ule,decide_eq_true_eq,apply_ite,HShiftRight.hShiftRight]

theorem source_canonical (x : U64) (h : x.val < 2147483647) :
    (PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64 x).val = x.val := by
  rw [source_shape,reduced_small x.bv h,BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by change x.val < 4294967296;omega)]
  rfl
#print axioms fold_small
#print axioms reduced_small
#print axioms source_shape
#print axioms source_canonical
end PV_B2_E_CtDecoder
