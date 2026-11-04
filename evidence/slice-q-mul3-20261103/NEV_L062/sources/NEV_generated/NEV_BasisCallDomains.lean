import NEV_BasisOuterStep
import NEI_PrefixProduct
set_option autoImplicit false
noncomputable section
namespace NEV_BasisCallDomains
open Aeneas Aeneas.Std Result AspisR1
/-- The SAME square result supplies double's canonical domain; the SAME
returned double supplies sub's. Reuse retained scalar total/value laws. -/
theorem scalar (node : U32) : ∃ square doubled out,
    NEV_AccumulateRaw.aspis_core.field.M31.mul node node=ok square ∧ square.val<2147483647 ∧
    NEV_AccumulateRaw.aspis_core.field.M31.double square=ok doubled ∧ doubled.val<2147483647 ∧
    NEV_AccumulateRaw.aspis_core.field.M31.sub doubled 1#u32=ok out ∧ out.val<2147483647 := by
  obtain ⟨square,actual,_,value,canonical⟩ := NEI_PrefixProduct.actual node node
  obtain ⟨doubled,hd,_,cd⟩ := ExtractedCurrentM31AddSub.current_add_mod square square canonical canonical
  obtain ⟨out,ho,_,co⟩ := ExtractedCurrentM31AddSub.current_sub_mod doubled 1#u32 cd (by decide)
  exact ⟨square,doubled,out,actual,canonical,
    (NEV_BasisOuterStep.double square).trans hd,cd,
    (NEV_BasisOuterStep.subtract doubled 1#u32).trans ho,co⟩
/-- Every active width64 level establishes the stricter native window. -/
theorem active_level (n fuel : Nat) (positive : 0<n) (schedule : n*2^(fuel+1)=64) :
    n≤32 ∧ n*2≤64 := by
  have power : 0<2^fuel := by positivity
  rw [pow_succ] at schedule
  nlinarith
#print axioms scalar
#print axioms active_level
end NEV_BasisCallDomains
end
