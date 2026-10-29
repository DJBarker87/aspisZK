import R1Z.PV_OWNI_RawOps
import R1Z.PV_OWNK_ReduceBits
set_option autoImplicit false
namespace R1Z.PV_OWNK_CTDecode
open Aeneas Aeneas.Std
abbrev subtract := PV_B2_FieldValue.aspis_core.field.ct.subtract_p
abbrev add := PV_B2_FieldValue.aspis_core.field.ct.add
abbrev sub := PV_B2_FieldValue.aspis_core.field.ct.sub
abbrev P := PV_B2_FieldValue.aspis_core.field.P

theorem sub_zero (x : U32) : U32.wrapping_sub x 0#u32 = x := by
 apply UScalar.eq_of_val_eq
 rw [U32.wrapping_sub_val_eq]
 simp only [show (0#u32).val=0 from rfl,Nat.sub_zero,Nat.add_mod_right]
 rw [UScalar.size]
 exact Nat.mod_eq_of_lt x.hBounds

theorem subtract_shape (x : U32) : subtract x =
 if x ≥ P then U32.wrapping_sub x P else x := by
 unfold subtract PV_B2_FieldValue.aspis_core.field.ct.subtract_p
 by_cases h : x ≥ P
 · simp only [h,decide_true,if_pos]
   rfl
 · simp only [h,decide_false,if_neg]
   change U32.wrapping_sub x 0#u32 = x
   exact sub_zero x

theorem subtract_decode (x : U32) (hx : x.val < 4294967294) :
 (subtract x).val = x.val % 2147483647 := by
 rw [subtract_shape]
 by_cases h : x ≥ P
 · rw [if_pos h,U32.wrapping_sub_val_eq,UScalar.size]
   change (x.val + (4294967296 - 2147483647)) % 4294967296 = x.val % 2147483647
   change 2147483647 ≤ x.val at h
   omega
 · rw [if_neg h]
   change ¬ 2147483647 ≤ x.val at h
   exact (Nat.mod_eq_of_lt (by omega)).symm

theorem add_decode (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (add a b).val = (a.val+b.val) % 2147483647 := by
 have hv : (core.num.U32.wrapping_add a b).val = a.val+b.val := by
  rw [core.num.U32.wrapping_add_val_eq,UScalar.size]
  change (a.val+b.val)%4294967296 = a.val+b.val
  omega
 unfold add PV_B2_FieldValue.aspis_core.field.ct.add
 rw [subtract_decode _ (by rw [hv];omega),hv]

theorem sub_decode (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (sub a b).val = (a.val+2147483647-b.val) % 2147483647 := by
 have hv : (core.num.U32.wrapping_sub (core.num.U32.wrapping_add a P) b).val = a.val+2147483647-b.val := by
  rw [core.num.U32.wrapping_sub_val_eq,core.num.U32.wrapping_add_val_eq,UScalar.size]
  change ((a.val+2147483647)%4294967296+(4294967296-b.val))%4294967296 = _
  omega
 unfold sub PV_B2_FieldValue.aspis_core.field.ct.sub
 rw [subtract_decode _ (by rw [hv];omega),hv]

/-- The CT reducer used by the actual raw multiplication, not the ordinary
arithmetic extraction's reducer. -/
theorem reduce_shape (x : U64) :
 (PV_B2_FieldValue.aspis_core.field.ct.reduce64 x).val =
 (PV_OWNK_ReduceBits.reduced x.bv).toNat := by
 unfold PV_B2_FieldValue.aspis_core.field.ct.reduce64
  PV_B2_FieldValue.aspis_core.field.ct.subtract_p
  PV_B2_FieldValue.aspis_core.field.P
 simp only [UScalar.lt_equiv,UScalar.le_equiv,UScalar.val,UScalar.cast,
  UScalar.cast_fromBool,UScalar.wrapping_shr,core.num.U32.wrapping_sub,
  U64.wrapping_add,U64.wrapping_shr,UScalar.wrapping_add,UScalar.wrapping_sub,
  UScalar.bv_and,UScalarTy.numBits,BitVec.zeroExtend_eq_setWidth,decide_eq_true_eq,
  U32.ofNat_bv]
 simp only [show BitVec.setWidth 64 2147483647#32 = 2147483647#64 from by decide,
  show (31#32).toNat % 64 = 31 from rfl,
  show (2147483647#32).toNat = 2147483647 from rfl]
 norm_num only [PV_OWNK_ReduceBits.reduced,PV_OWNK_ReduceBits.word,
  PV_OWNK_ReduceBits.fold64,BitVec.ule,decide_eq_true_eq,apply_ite,HShiftRight.hShiftRight]

theorem reduce_decode (x : U64) :
 (PV_B2_FieldValue.aspis_core.field.ct.reduce64 x).val = x.val % 2147483647 := by
 rw [reduce_shape,PV_OWNK_ReduceBits.decode]
 rfl

theorem reduce_canon (x : U64) :
 (PV_B2_FieldValue.aspis_core.field.ct.reduce64 x).val < 2147483647 := by
 rw [reduce_decode]
 exact Nat.mod_lt _ (by omega)

theorem add_canon (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (add a b).val < 2147483647 := by
 rw [add_decode a b ha hb]
 exact Nat.mod_lt _ (by omega)

theorem sub_canon (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (sub a b).val < 2147483647 := by
 rw [sub_decode a b ha hb]
 exact Nat.mod_lt _ (by omega)

#print axioms reduce_shape
#print axioms reduce_decode
#print axioms reduce_canon
#print axioms add_canon
#print axioms sub_canon
#print axioms sub_zero
#print axioms subtract_shape
#print axioms subtract_decode
#print axioms add_decode
#print axioms sub_decode
end R1Z.PV_OWNK_CTDecode
