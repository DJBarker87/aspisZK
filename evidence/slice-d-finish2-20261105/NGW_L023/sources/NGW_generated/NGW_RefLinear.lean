import NGW_HelperRef.Funs
import NGM_ReferenceLinear
import NGM_ProbeTransport
set_option autoImplicit false
namespace NGW_RefLinear
open Aeneas Aeneas.Std Result AspisR1
abbrev P : Nat := 2147483647

theorem add (x y : U32) :
 NGW_HelperRef.add_ref x y=FIn_WeightsExtract.field.M31.add x y := by
 simp [NGW_HelperRef.add_ref,FIn_WeightsExtract.field.M31.add,FIn_WeightsExtract.field.P,lift]

theorem sub (x y : U32) :
 NGW_HelperRef.sub_ref x y=FIn_WeightsExtract.field.M31.sub x y := by
 simp [NGW_HelperRef.sub_ref,FIn_WeightsExtract.field.M31.sub,FIn_WeightsExtract.field.P,lift]

theorem sub_total (x y : U32) (hx : x.val<P) (hy : y.val<P) :
 ∃ z,FIn_WeightsExtract.field.M31.sub x y=ok z ∧ z.val<P := by
 obtain ⟨z,hz,_,hc⟩ := LPi_NatBase.sub x y hx hy
 exact ⟨z,(NGM_ProbeTransport.base_sub x y).trans hz,hc⟩

theorem cell (bit carry product : U32) (hb : bit.val<P) (hc : carry.val<P) (hp : product.val<P) :
 ∃ sum twice value,
 FIn_WeightsExtract.field.M31.add bit carry=ok sum ∧
 FIn_WeightsExtract.field.M31.add product product=ok twice ∧
 FIn_WeightsExtract.field.M31.sub sum twice=ok value ∧ value.val<P := by
 obtain ⟨sum,hs,cs⟩ := NGM_ReferenceLinear.add_canonical bit carry hb hc
 obtain ⟨twice,ht,ct⟩ := NGM_ReferenceLinear.add_canonical product product hp hp
 obtain ⟨value,hv,cv⟩ := sub_total sum twice cs ct
 exact ⟨sum,twice,value,hs,ht,hv,cv⟩

#print axioms add
#print axioms sub
#print axioms sub_total
#print axioms cell
end NGW_RefLinear
