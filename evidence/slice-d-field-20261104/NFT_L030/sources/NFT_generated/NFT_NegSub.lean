import NFT_NegWord
set_option autoImplicit false
namespace NFT_NegSub
open Aeneas Aeneas.Std Result

theorem scalar (x : U32) (canonical : x.val<2147483647) :
    AspisR1CurrentWide.field.M31.sub 0#u32 x=AspisR1SelectedMaskProbe.field.M31.neg x := by
  have carrier : AspisR1CurrentWide.field.M31.sub 0#u32 x=
      AspisR1SelectedMaskProbe.field.M31.sub 0#u32 x := by
    simp only [AspisR1CurrentWide.field.M31.sub,AspisR1SelectedMaskProbe.field.M31.sub,
      AspisR1CurrentWide.field.P,AspisR1SelectedMaskProbe.field.P]
  obtain ⟨a,ra,va,ca⟩:=AspisR1.ExtractedMaskM31AddSub.current_sub_mod 0#u32 x (by decide) canonical
  obtain ⟨b,rb,cb,vb⟩:=AspisR1.ExtractedMaskNeg.current_neg_mod x canonical
  have same : a=b := by
    apply UScalar.eq_of_val_eq
    simpa only [show (0#u32).val=0 from rfl,Nat.zero_add] using va.trans vb.symm
  rw [carrier,ra,rb,same]

#print axioms scalar
end NFT_NegSub
