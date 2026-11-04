import NFG_InverseRef.Funs
import NFG_ResultCongr
set_option autoImplicit false
namespace NFG_InvWithCuts
open Aeneas Aeneas.Std Result NFG_InverseRef
/-- These seven cuts come from one emitted computation. This is a model cut
law; generic backend dispatch has no native credit. -/
theorem accepted (x out : field.CM31) (backend : U32 → Result U32)
 (run : field.CM31.inv_with x backend=ok out) :
 ∃ aa bb norm inverse real negative imag : U32,
 field.M31.mul x.a x.a=ok aa ∧ field.M31.mul x.b x.b=ok bb ∧
 field.M31.add aa bb=ok norm ∧ backend norm=ok inverse ∧
 field.M31.mul x.a inverse=ok real ∧ field.M31.neg x.b=ok negative ∧
 field.M31.mul negative inverse=ok imag ∧ out=⟨real,imag⟩ := by
 unfold field.CM31.inv_with at run
 obtain ⟨aa,ha,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨bb,hb,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨norm,hn,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨inverse,hi,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨real,hr,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨negative,hg,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 obtain ⟨imag,hm,run⟩ := NFG_ResultCongr.bind_success _ _ _ run
 exact ⟨aa,bb,norm,inverse,real,negative,imag,ha,hb,hn,hi,hr,hg,hm,(Result.ok.inj run).symm⟩
/-- Only the adopted direct edge is selected. No function-pointer comparison. -/
theorem selected (x : field.CM31) :
 field.CM31.inv x=field.CM31.inv_with x field.M31.inv := rfl
#print axioms accepted
#print axioms selected
end NFG_InvWithCuts
