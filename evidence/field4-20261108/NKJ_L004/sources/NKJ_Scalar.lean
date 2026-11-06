import NKJ_Extracted.Funs
import NFT_ChannelFour
set_option autoImplicit false
namespace NKJ_Scalar
open Aeneas Aeneas.Std Result
abbrev R := NKJ_Extracted.field.NKJ_reference.NKJ_product

theorem product (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
 ∃ p : U64, R a b=ok p ∧ p.val=a.val*b.val ∧
 UScalar.mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)=ok p := by
 obtain ⟨p,hp,hv⟩ := NFT_Dot.scalar_product a b ha hb
 have bound : a.val*b.val<2^64 := by
  exact Nat.lt_trans (NFT_ChannelModel.product_bound a.val b.val ha hb) (by norm_num)
 have hw : (U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b)).val=p.val := by
  rw [U64.wrapping_mul_val_eq,AspisR1.ExtractedMaskReducer.cast_widen_value,
   AspisR1.ExtractedMaskReducer.cast_widen_value,hv]
  exact Nat.mod_eq_of_lt bound
 have same := UScalar.eq_of_val_eq hw
 refine ⟨p,?_,hv,hp⟩
 change ok (U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b))=ok p
 rw [same]
#print axioms product
end NKJ_Scalar
