import R1Z.PV_RDB2C_PV_B2_C_251FieldTotal
import R1Z.PV_RDB2C_PV_B2_D_ReducerBounds
set_option autoImplicit false
namespace PV_B2_D_ScalarCanonical
open Aeneas Aeneas.Std
abbrev F := PV_B2_C_251FieldValue.aspis_core.field.P
abbrev reduce := PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64
open PV_B2_D_ReducerBounds

theorem reduce_bound (x : U64) : reduce x < F := by
  unfold reduce PV_B2_C_251FieldValue.aspis_core.field.ct.reduce64
    PV_B2_C_251FieldValue.aspis_core.field.ct.subtract_p F
    PV_B2_C_251FieldValue.aspis_core.field.P
  simp only [UScalar.lt_equiv,UScalar.le_equiv,UScalar.val,UScalar.cast,
    UScalar.cast_fromBool,UScalar.wrapping_shr,core.num.U32.wrapping_sub,
    U64.wrapping_add,U64.wrapping_shr,UScalar.wrapping_add,UScalar.wrapping_sub,
    UScalar.bv_and,UScalarTy.numBits,BitVec.zeroExtend_eq_setWidth,decide_eq_true_eq,
    U32.ofNat_bv]
  simp only [show BitVec.setWidth 64 2147483647#32 = 2147483647#64 from by decide,
    show (31#32).toNat % 64 = 31 from rfl,
    show (2147483647#32).toNat = 2147483647 from rfl]
  have h := bitvec_bound x.bv
  norm_num only [reduced,word,fold64,BitVec.ule,decide_eq_true_eq,apply_ite,
    HShiftRight.hShiftRight] at h ⊢
  exact h
#print axioms reduce_bound
end PV_B2_D_ScalarCanonical
