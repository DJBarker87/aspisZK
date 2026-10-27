import XSa_CheckedQ
import JGi_QRawSourceForwardTotalityV1
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XSa_QRawTotal

def canonical (q : E.Q) : Prop :=
 q.c0.a.val<2147483647 ∧ q.c0.b.val<2147483647 ∧
 q.c1.a.val<2147483647 ∧ q.c1.b.val<2147483647

theorem total (a b : E.Q) (ha : canonical a) (hb : canonical b) :
 ∃ out, AspisR1EbyKPushDecodedProductUpdate.QRaw (XRn_Join_toQ a) (XRn_Join_toQ b)=ok out := by
 apply AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs
 all_goals simp only [XRn_Join_toQ,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ]
 all_goals unfold canonical at ha hb
 all_goals omega

#print axioms total
end XSa_QRawTotal
