import XSa_CheckedQ
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotCarriers
set_option autoImplicit false
namespace XSa_DotControl
open AspisR1ClaimPreparedBridge

theorem push (raw : AspisR1EbyKPushDotBackend.RawFn) (a b : Dot)
 (count : Usize) (v : C.E) (q : E.Q) :
 AspisR1EbyKPushDotBackend.pushWithDotBackend raw (state a b count)
   (AspisR1S5ClaimDotConcreteAdapter.toPushWide (toClaimE v)) (XSa_CheckedQ.scalar q) =
 (if count≥AspisR1EbyKPushExplicitOpsV1.maxTerms then ok (.Err (),state a b count)
  else if XSa_CheckedQ.valid q then do
   let lo ← AspisR1EbyKPushDotBackend.dotViaRaw raw ⟨a.sums⟩ (XRn_Join_toQ (eq v.c0)) (XRn_Join_toQ q)
   let hi ← AspisR1EbyKPushDotBackend.dotViaRaw raw ⟨b.sums⟩ (XRn_Join_toQ (eq v.c1)) (XRn_Join_toQ q)
   let next ← count+1#usize
   ok (.Ok (),⟨lo,hi,next⟩)
  else ok (.Err (),state a b count)) := by
 unfold AspisR1EbyKPushDotBackend.pushWithDotBackend
   AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
   AspisR1EbyKPushSourceConversionV1.pushWithSourceCheckedAdd
   AspisR1EbyKPushSourceConversionV1.pushWithSourceConversion
   AspisR1EbyKPushExplicitOpsV1.pushWithOps
 by_cases hc : count≥AspisR1EbyKPushExplicitOpsV1.maxTerms
 · simp only [state,hc,if_true]
 · simp only [state,hc,if_false]
   rw [AspisR1EbyKPushWideToQ.fromWide_coordinates,bind_tc_ok]
   simp only [AspisR1EbyKPushWideToQ.pairFromCoords,
     AspisR1EbyKPushWideToQ.qFromCoords,Array.index_usize,Array.make,bind_tc_ok]
   rw [XSa_CheckedQ.checked]
   split_ifs <;> rfl

#print axioms push
end XSa_DotControl
