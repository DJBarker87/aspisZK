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
 (if count≥AspisR1EbyKPushExplicitOpsV1.maxTerms then ok (core.result.Result.Err (),state a b count)
  else if XSa_CheckedQ.valid q then do
   let lo ← AspisR1EbyKPushDotBackend.dotViaRaw raw ⟨a.sums⟩ (XRn_Join_toQ (eq v.c0)) (XRn_Join_toQ q)
   let hi ← AspisR1EbyKPushDotBackend.dotViaRaw raw ⟨b.sums⟩ (XRn_Join_toQ (eq v.c1)) (XRn_Join_toQ q)
   let next ← count+1#usize
   ok (core.result.Result.Ok (),⟨lo,hi,next⟩)
  else ok (core.result.Result.Err (),state a b count)) := by
 unfold AspisR1EbyKPushDotBackend.pushWithDotBackend
   AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
   AspisR1EbyKPushSourceConversionV1.pushWithSourceCheckedAdd
   AspisR1EbyKPushSourceConversionV1.pushWithSourceConversion
   AspisR1EbyKPushExplicitOpsV1.pushWithOps
 by_cases hc : count≥AspisR1EbyKPushExplicitOpsV1.maxTerms
 · simp only [state,hc,if_true]
 · simp only [state,hc,if_false]
   have hw : AspisR1EbyKPushWideToQ.fromWide
       (AspisR1S5ClaimDotConcreteAdapter.toPushWide (toClaimE v)) =
       ok (Array.make 2#usize [XRn_Join_toQ (eq v.c0),XRn_Join_toQ (eq v.c1)]) :=
     AspisR1EbyKPushWideToQ.fromWide_coordinates _
   have h0 : Array.index_usize (Array.make 2#usize [XRn_Join_toQ (eq v.c0),XRn_Join_toQ (eq v.c1)]) 0#usize =
     ok (XRn_Join_toQ (eq v.c0)) := rfl
   have h1 : Array.index_usize (Array.make 2#usize [XRn_Join_toQ (eq v.c0),XRn_Join_toQ (eq v.c1)]) 1#usize =
     ok (XRn_Join_toQ (eq v.c1)) := rfl
   have hq : AspisR1EbyKPushConcreteCheckedQV1.checkedQWithAll
       AspisR1EbyKCheckedQConcreteAll.concreteAll (XSa_CheckedQ.scalar q) =
       ok (if XSa_CheckedQ.valid q then .Ok (XRn_Join_toQ q) else .Err ()) := XSa_CheckedQ.checked q
   rw [hw,bind_tc_ok,h0,bind_tc_ok,h1,bind_tc_ok,hq]
   split_ifs <;> rfl

#print axioms push
end XSa_DotControl
