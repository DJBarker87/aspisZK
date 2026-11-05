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

theorem sub (x y : U32) (hx : x.val<P) (hy : y.val<P) :
 NGW_HelperRef.sub_ref x y=FIn_WeightsExtract.field.M31.sub x y := by
 change x.val<2147483647 at hx
 change y.val<2147483647 at hy
 let a := U32.wrapping_add x 2147483647#u32
 have av : a.val=x.val+2147483647 := by
  rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  rfl
 let t := U32.wrapping_sub a y
 have tv : t.val=x.val+2147483647-y.val := by
  rw [LPi_NatBase.sub_word a y (by rw [av]; omega),av]
 simp only [NGW_HelperRef.sub_ref,FIn_WeightsExtract.field.M31.sub,FIn_WeightsExtract.field.P,lift,bind_tc_ok]
 change (if x≥y then ok (U32.wrapping_sub x y) else ok t)=
   (if t≥2147483647#u32 then ok (U32.wrapping_sub t 2147483647#u32) else ok t)
 by_cases h : x≥y
 · have ht : t≥2147483647#u32 := by scalar_tac
   rw [if_pos h,if_pos ht]
   apply congrArg Result.ok
   apply UScalar.eq_of_val_eq
   rw [LPi_NatBase.sub_word x y (by scalar_tac),LPi_NatBase.sub_word t 2147483647#u32 (by scalar_tac)]
   change _=t.val-2147483647
   rw [tv]
   scalar_tac
 · have ht : ¬t≥2147483647#u32 := by scalar_tac
   rw [if_neg h,if_neg ht]


theorem sub_total (x y : U32) (hx : x.val<P) (hy : y.val<P) :
 ∃ z,FIn_WeightsExtract.field.M31.sub x y=ok z ∧ z.val<P := by
 obtain ⟨z,hz,_,hc⟩ := LPi_NatBase.sub x y hx hy
 exact ⟨z,(NGM_ProbeTransport.base_sub x y).trans hz,hc⟩

theorem cell (bit carry product : U32) (hb : bit.val<P) (hc : carry.val<P) (hp : product.val<P) :
 ∃ sum twice value,
 FIn_WeightsExtract.field.M31.add bit carry=ok sum ∧
 FIn_WeightsExtract.field.M31.add product product=ok twice ∧
 FIn_WeightsExtract.field.M31.sub sum twice=ok value ∧ sum.val<P ∧ twice.val<P ∧ value.val<P := by
 obtain ⟨sum,hs,cs⟩ := NGM_ReferenceLinear.add_canonical bit carry hb hc
 obtain ⟨twice,ht,ct⟩ := NGM_ReferenceLinear.add_canonical product product hp hp
 obtain ⟨value,hv,cv⟩ := sub_total sum twice cs ct
 exact ⟨sum,twice,value,hs,ht,hv,cs,ct,cv⟩

#print axioms add
#print axioms sub
#print axioms sub_total
#print axioms cell
end NGW_RefLinear
