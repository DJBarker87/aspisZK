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
  apply Nat.mod_eq_of_lt
  rw [UScalar.size_def]
  scalar_tac
 have same := UScalar.eq_of_val_eq hw
 refine ⟨p,?_,hv,hp⟩
 change ok (U64.wrapping_mul (UScalar.cast .U64 a) (UScalar.cast .U64 b))=ok p
 rw [same]
#print axioms product
end NKJ_Scalar

namespace NKJ_Scalar
open Aeneas Aeneas.Std Result

theorem wrapping_add_value (s p : U64) (h : s.val+p.val<2^64) :
 (U64.wrapping_add s p).val=s.val+p.val := by
 rw [U64.wrapping_add_val_eq]
 apply Nat.mod_eq_of_lt
 rw [UScalar.size_def]
 scalar_tac

def update (s : U64) (a b : U32) : Result U64 := do
 let p ← R a b
 ok (U64.wrapping_add s p)

theorem update_value (s : U64) (a b : U32)
 (ha : a.val<2147483647) (hb : b.val<2147483647)
 (hs : s.val≤3*(2147483647-1)^2) :
 ∃ out : U64, update s a b=ok out ∧ out.val=s.val+a.val*b.val ∧
 AspisR1PoseidonPreparedChannelGeneratedStep.generatedChannelUpdate a b s=ok out := by
 obtain ⟨p,hp,hpv,_⟩ := product a b ha hb
 have prodBound : a.val*b.val≤(2147483647-1)^2 := by
  calc
   a.val*b.val≤(2147483647-1)*(2147483647-1) := Nat.mul_le_mul (by omega) (by omega)
   _=(2147483647-1)^2 := by ring
 have sumBound : s.val+p.val<2^64 := by rw [hpv];omega
 obtain ⟨out,ho,hv⟩ := NFT_ChannelFour.generated_step a b s ha hb hs
 have same : U64.wrapping_add s p=out := by
  apply UScalar.eq_of_val_eq
  rw [wrapping_add_value s p sumBound,hpv,hv]
 refine ⟨out,?_,hv,ho⟩
 simp only [update,hp,bind_tc_ok,same]
#print axioms wrapping_add_value
#print axioms update_value
end NKJ_Scalar
