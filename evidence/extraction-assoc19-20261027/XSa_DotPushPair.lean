import XSa_DotActual
import XSa_DotControl
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers
set_option autoImplicit false
namespace XSa_DotPushPair
open AspisR1ClaimPreparedBridge

theorem paired (a b : Dot) (count : Usize) (hc : count.val<29)
 (v : C.E) (hv : XRy_WideMultiply.Canonical v) (q : E.Q) (hq : XSa_CheckedQ.valid q=true) :
 ∃ a' b' next,
 _root_.fast_pairing.canonical.Dot.push a (XRn_Join_toQ (eq v.c0)) (XRn_Join_toQ q)=ok a' ∧
 _root_.fast_pairing.canonical.Dot.push b (XRn_Join_toQ (eq v.c1)) (XRn_Join_toQ q)=ok b' ∧
 (count+1#usize : Result Usize)=ok next ∧ next.val=count.val+1 ∧
 ops.pushDot (state a b count) (toClaimE v) (toClaimQ (cq q))=ok (.Ok (),state a' b' next) := by
 have hcan : XSa_QRawTotal.canonical q := by
   unfold XSa_CheckedQ.valid at hq
   simp only [Bool.and_eq_true,decide_eq_true_eq] at hq
   unfold XSa_QRawTotal.canonical
   scalar_tac
 have hlo : XSa_QRawTotal.canonical (eq v.c0) := ⟨hv.1.1.1,hv.1.1.2,hv.1.2.1,hv.1.2.2⟩
 have hhi : XSa_QRawTotal.canonical (eq v.c1) := ⟨hv.2.1.1,hv.2.1.2,hv.2.2.1,hv.2.2.2⟩
 obtain ⟨a',ra,ta⟩ := XSa_DotActual.push a (eq v.c0) q hlo hcan
 obtain ⟨b',rb,tb⟩ := XSa_DotActual.push b (eq v.c1) q hhi hcan
 obtain ⟨next,en,hn⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=count) (y:=1#usize) (by scalar_tac))
 refine ⟨a',b',next,ra,rb,en,hn,?_⟩
 change AspisR1EbyKPushDotBackend.pushWithDotBackend _ (state a b count)
   (AspisR1S5ClaimDotConcreteAdapter.toPushWide (toClaimE v)) (XSa_CheckedQ.scalar q)=_
 rw [XSa_DotControl.push]
 have hb : ¬count≥AspisR1EbyKPushExplicitOpsV1.maxTerms := by
   unfold AspisR1EbyKPushExplicitOpsV1.maxTerms
   scalar_tac
 simp only [hb,if_false,hq,if_true,ta,tb,en,bind_tc_ok]
 rfl

#print axioms paired
end XSa_DotPushPair
