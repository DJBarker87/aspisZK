import NKE_ResumeClauses1
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
theorem queryEndG  (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) (r28 : verifier.Reader)  :
 NKE_EventAll.Holds Clause (NJU_ResumeObserved.queryEndG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r28) := by
 simp only [NJU_ResumeObserved.queryEndG,NJU_Log.prod_cases,NJU_ResumeObserved.recordRaw,NJU_ResumeObserved.recordK,NJU_ResumeObserved.recordE,NJU_ResumeObserved.recordSemantic,NJU_ResumeObserved.recordWeights,NJU_ResumeObserved.recordValidate,NJU_ResumeObserved.recordFilled,NJU_ResumeObserved.recordAny,NJU_ResumeObserved.recordDigest]
 repeat' first
 | nke_zeta
 | nke_bind
 | nke_intro
 | nke_lift
 | nke_pure
 | nke_resume_record
 | (apply NKE_ResumeClauses.finishTailG)
 | split
#print axioms queryEndG
end NKE_ResumeClauses
