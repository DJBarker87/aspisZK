import XSa_DotPushPair
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers
set_option autoImplicit false
namespace XSa_DotReject
open AspisR1ClaimPreparedBridge

theorem reject (a b : Dot) (count : Usize) (hc : count.val<29)
 (v : C.E) (q : E.Q) (hq : XSa_CheckedQ.valid q=false) :
 ops.pushDot (state a b count) (toClaimE v) (toClaimQ (cq q))=
 ok (.Err (),state a b count) := by
 change AspisR1EbyKPushDotBackend.pushWithDotBackend _ (state a b count)
   (AspisR1S5ClaimDotConcreteAdapter.toPushWide (toClaimE v)) (XSa_CheckedQ.scalar q)=_
 rw [XSa_DotControl.push]
 have hb : ¬count≥AspisR1EbyKPushExplicitOpsV1.maxTerms := by
   unfold AspisR1EbyKPushExplicitOpsV1.maxTerms
   scalar_tac
 simp only [hb,if_false,hq,Bool.false_eq_true,if_false]

#print axioms reject
end XSa_DotReject
