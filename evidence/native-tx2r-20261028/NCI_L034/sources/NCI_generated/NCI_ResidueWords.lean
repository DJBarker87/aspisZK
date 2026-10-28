import NCI_ResidueBounds
import Aeneas
set_option autoImplicit false
namespace AspisR1.NCI_ResidueWords
open Aeneas Aeneas.Std Result NCI_ResidueBounds

theorem word_exists (value : Nat) (bound : value<18446744073709551616) :
    ∃ w : U64, UScalar.tryMk .U64 value=ok w ∧ w.val=value := by
  have check : UScalar.check_bounds .U64 value=true := by
    simp [UScalar.check_bounds,UScalar.cMax,UScalarTy.numBits]
    omega
  simp only [UScalar.tryMk,UScalar.tryMkOpt,check,dif_pos,Result.ofOption]
  exact ⟨_,rfl,rfl⟩

theorem product_sum (a b : U32) (raw : U64) (terms : Nat)
    (ha : a.val<P) (hb : b.val<P)
    (hr : raw.val<Boundary+(terms%4)*MaxProduct) :
    ∃ product sum : U64,
      (UScalar.cast .U64 a * UScalar.cast .U64 b)=ok product ∧
      product.val=a.val*b.val ∧ raw+product=ok sum ∧
      sum.val=raw.val+a.val*b.val := by
  have prodBound := product_bound a.val b.val ha hb
  have productFits : a.val*b.val<18446744073709551616 := by
    simp only [MaxProduct] at prodBound
    omega
  have sumFits := group_nowrap raw.val (a.val*b.val) (terms%4)
    (Nat.mod_lt _ (by decide)) hr prodBound
  obtain ⟨product,hproduct,value⟩ := word_exists (a.val*b.val) productFits
  obtain ⟨sum,hsum,total⟩ := word_exists (raw.val+a.val*b.val) sumFits
  have ca : (UScalar.cast .U64 a).val=a.val := by scalar_tac
  have cb : (UScalar.cast .U64 b).val=b.val := by scalar_tac
  refine ⟨product,sum,?_,value,?_,total⟩
  · change UScalar.tryMk .U64 ((UScalar.cast .U64 a).val*(UScalar.cast .U64 b).val)=ok product
    rw [ca,cb]
    exact hproduct
  · change UScalar.tryMk .U64 (raw.val+product.val)=ok sum
    rw [value]
    exact hsum
#print axioms word_exists
#print axioms product_sum
end AspisR1.NCI_ResidueWords
