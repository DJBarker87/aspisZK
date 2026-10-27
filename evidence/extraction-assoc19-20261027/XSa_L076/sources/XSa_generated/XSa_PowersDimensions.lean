import XSa_PowersArray
import XSa_PartAssociation
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers
set_option autoImplicit false
namespace XSa_PowersDimensions
open AspisR1ClaimPreparedBridge

theorem seven (x : C.E) (hx : XRy_WideMultiply.Canonical x) :
 ∃ k : XRy_ClaimSumStep.Seven,
 XRn_Join_powers x 7 XRy_Powers.one=ok k.val ∧
 ops.powers 7#usize (toClaimE x)=ok (arr toClaimE k) ∧ XRy_ClaimSumStep.canonical k := by
 obtain ⟨k,hr,hlist,hcan,ht⟩ := XSa_PowersArray.powers 7#usize x hx
 refine ⟨k,hlist,ht,?_⟩
 intro i hi
 exact hcan _ (List.getElem_mem _)

theorem twenty_nine (x : C.E) (hx : XRy_WideMultiply.Canonical x) :
 ∃ g : XSa_DotRun.Coeff, XRn_Join_Release.weights.powers 29#usize x=ok g ∧
 AspisR1ClaimPreparedBridge.powersPublic 29#usize x=ok g ∧ XSa_DotRun.canonical g := by
 obtain ⟨g,hr,hlist,hcan,ht⟩ := XSa_PowersArray.powers 29#usize x hx
 refine ⟨g,hr,(XRy_PowersPublic.powers 29#usize x hx).symm.trans hr,?_⟩
 intro i hi
 exact hcan _ (List.getElem_mem _)

#print axioms seven
#print axioms twenty_nine
end XSa_PowersDimensions
