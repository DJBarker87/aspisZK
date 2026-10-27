import LPm_RawPort
set_option autoImplicit false
namespace AspisR1.LPm_UpdatePort
open Aeneas Aeneas.Std Result
#print AspisR1DotPushLocal.Proof.updateWord
#print AspisR1EbyKPushDotBackend.dotViaRaw

def dotPort (s : LPm_PublicState.Dot) : AspisR1EbyKPushDotBackend.PushDot := ⟨s.sums⟩

theorem word (s r : U64) :
    LPf_DotPushFour.update s r = AspisR1DotPushLocal.Proof.updateWord s r := by
  rfl

theorem sums (s : LPm_PublicState.Dot) (r : LPm_PublicState.Raw) :
    (dotPort (LPm_PublicState.update s r)).sums =
      AspisR1DotPushLocal.Proof.updatedSums (dotPort s).sums r := by
  obtain ⟨s0,s1,s2,s3,ss⟩ := LPf_ArrayFour.shape s.sums
  obtain ⟨r0,r1,r2,r3,rr⟩ := LPf_ArrayFour.shape r
  simp only [dotPort,LPm_PublicState.update,AspisR1DotPushLocal.Proof.updatedSums,
    ss,rr,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ,List.zipWith_cons,
    List.zipWith_nil,word]

#print axioms word
#print axioms sums
end AspisR1.LPm_UpdatePort
