import NGW_PointValue
import NGW_StepModel
import NGW_ConstructorArrays
set_option autoImplicit false
namespace NGW_CellPacket
open Aeneas Aeneas.Std Result NGW_ConstructorQM NGW_ConstructorArrays

theorem cohort (z successor : Array Q 10#usize) (carry : Q) (i : Usize)
    (hz : Holds Canon z) (hs : Holds Canon successor) (hc : Canon carry)
    (bound : i.val<10) :
 ∃ bit product value out,
 Array.index_usize z i=ok bit ∧
 FIn_WeightsExtract.field.QM31.mul bit carry=ok product ∧
 Canon product ∧
 AspisR1.LPi_FieldValues.qw (NGM_ProbeTransport.toQ product)=
   AspisR1.LPi_FieldValues.mulQ (AspisR1.LPi_FieldValues.qw (NGM_ProbeTransport.toQ bit))
     (AspisR1.LPi_FieldValues.qw (NGM_ProbeTransport.toQ carry)) ∧
 NGW_HelperRef.point_ref (NGW_PointValue.words bit) (NGW_PointValue.words carry)
   (NGW_PointValue.words product)=ok (NGW_PointValue.words value) ∧
 Array.update successor i value=ok out ∧
 NGW_StepModel.step z successor carry i=ok (out,product) ∧
 Holds Canon out := by
 let bit := NGM_GuardExact.pick z i.val bound
 have read := NGM_GuardExact.index z i bound
 change Array.index_usize z i=ok bit at read
 have cb := canonical_pick Canon z i.val bound hz
 obtain ⟨product,hm,cp,natural⟩ := NGW_ProductLaw.total bit carry cb hc
 obtain ⟨sum,ha,ca⟩ := add bit carry cb hc
 obtain ⟨twice,ht,ct⟩ := add product product cp cp
 obtain ⟨value,hv,cv⟩ := sub sum twice ca ct
 let out := put successor i.val value
 have update := NGW_ConstructorArrays.update successor i value bound
 change Array.update successor i value=ok out at update
 have observed := NGW_PointValue.observed bit carry product cb hc cp
 simp only [NGW_PointValue.arithmetic,ha,ht,hv,bind_tc_ok] at observed
 refine ⟨bit,product,value,out,read,hm,cp,natural,observed,update,?_,canonical_put Canon successor i.val value hs cv⟩
 simp only [NGW_StepModel.step,read,hm,ha,ht,hv,update,bind_tc_ok]

#print axioms cohort
end NGW_CellPacket
