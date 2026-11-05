import NHE_DotRaw
import NFE_NFC_DotPushCut
set_option autoImplicit false
namespace NHE_PrivateDot
open Aeneas Aeneas.Std Result AspisR1
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev PushDot := AspisR1EbyKPushDotBackend.PushDot
abbrev Q := FIo_Native.fast_pairing.canonical.Q

def toPush (d : Dot) : PushDot := ⟨d.sums⟩

theorem update (s r : U64) :
 NFE_NFC_DotPushFour.update s r=AspisR1DotPushLocal.Proof.updateWord s r := by rfl

theorem cohort (d : Dot) (a b : Q) :
 FIo_FieldBridge.map toPush (FIo_Native.fast_pairing.canonical.Dot.push d a b)=
 AspisR1EbyKPushDotBackend.dotViaRaw AspisR1EbyKPushDecodedProductUpdate.QRaw (toPush d) a b := by
 rcases d with ⟨sums⟩
 obtain ⟨s0,s1,s2,s3,hs⟩ := NGM_ArrayFour.shape sums
 subst sums
 cases raw : FIo_Native.fast_pairing.canonical.Q.raw a b with
 | fail e =>
  simp only [FIo_Native.fast_pairing.canonical.Dot.push,raw,bind_tc_fail,FIo_FieldBridge.map,AspisR1EbyKPushDotBackend.dotViaRaw,AspisR1DotPushLocal.canonical.Dot.push,←NHE_DotRaw.raw]
  rw [raw]
  rfl
 | div =>
  simp only [FIo_Native.fast_pairing.canonical.Dot.push,raw,bind_tc_div,FIo_FieldBridge.map,AspisR1EbyKPushDotBackend.dotViaRaw,AspisR1DotPushLocal.canonical.Dot.push,←NHE_DotRaw.raw]
  rw [raw]
  rfl
 | ok words =>
  obtain ⟨r0,r1,r2,r3,hr⟩ := NGM_ArrayFour.shape words
  subst words
  have actual := NFE_NFC_DotPushCut.source a b s0 s1 s2 s3 r0 r1 r2 r3 raw
  have currentRaw := (NHE_DotRaw.raw a b).symm.trans raw
  have current := AspisR1DotPushLocal.Proof.push_four_coordinates
   AspisR1EbyKPushDecodedProductUpdate.QRaw a b s0 s1 s2 s3 r0 r1 r2 r3 currentRaw
  simp only [actual,FIo_FieldBridge.map,toPush,AspisR1EbyKPushDotBackend.dotViaRaw,current,bind_tc_ok,update]

#print axioms update
#print axioms cohort
end NHE_PrivateDot
