import NFT_Reference.Funs
import NFQ_FieldLaws
set_option autoImplicit false
namespace NFT_NegWord
open Aeneas Aeneas.Std Result

theorem wrapping_value (x : U32) (canonical : x.val<2147483647) :
    (U32.wrapping_sub 2147483647#u32 x).val=2147483647-x.val := by
  have size : U32.size=4294967296 := by simp [U32.size,U32.numBits]
  simp [U32.wrapping_sub,size]
  omega

theorem source (x : U32) (canonical : x.val<2147483647) :
    NFT_Reference.neg_ref x=AspisR1SelectedMaskProbe.field.M31.neg x := by
  by_cases zero : x=0#u32
  · subst x;rfl
  · have nz : x.val≠0 := by intro h;apply zero;apply UScalar.eq_of_val_eq;exact h
    obtain ⟨z,run,value,bound⟩:=NFQ_FieldLaws.neg_value x canonical
    have same : U32.wrapping_sub 2147483647#u32 x=z := by
      apply UScalar.eq_of_val_eq
      rw [wrapping_value x canonical,value,if_neg nz]
    simp only [NFT_Reference.neg_ref,if_neg zero,same,run]

#print axioms wrapping_value
#print axioms source
end NFT_NegWord
