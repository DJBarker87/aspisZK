import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NJU_ResumeErase
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

theorem finishTail (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (queryValues : Array U32 22#usize) (r34 : verifier.Reader) :
 (finishTailG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues r34).result=finishTailR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues r34 := by
 simp only [finishTailG,finishTailR,recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases]
 repeat' first
 | (intro hypothesis)
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases])
 | split
 | rfl
 all_goals simp_all only [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases]

theorem queryEnd (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) (r28 : verifier.Reader) :
 (queryEndG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r28).result=queryEndR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r28 := by
 simp only [queryEndG,queryEndR,recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail]
 repeat' first
 | (intro hypothesis)
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail])
 | split
 | rfl
 all_goals simp_all only [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail]

theorem queryMid (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 : U32) (r20 : verifier.Reader) :
 (queryMidG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 r20).result=queryMidR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 r20 := by
 simp only [queryMidG,queryMidR,recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd]
 repeat' first
 | (intro hypothesis)
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd])
 | split
 | rfl
 all_goals simp_all only [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd]

theorem queryBlock (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (r12 : verifier.Reader) :
 (queryBlockG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r12).result=queryBlockR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r12 := by
 simp only [queryBlockG,queryBlockR,recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid]
 repeat' first
 | (intro hypothesis)
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid])
 | split
 | rfl
 all_goals simp_all only [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid]

theorem resumeBody (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize) :
 (resumeBodyG reservation d bytes v i4 end1).result=resumeBodyR reservation d bytes v i4 end1 := by
 simp only [resumeBodyG,resumeBodyR,recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid,queryBlock]
 repeat' first
 | (intro hypothesis)
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid,queryBlock])
 | split
 | rfl
 all_goals simp_all only [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid,queryBlock]

theorem header (reservation : NP6_StdModel.Reservation)
  {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
  (bytes : Slice Std.U8) (proof : Slice Std.U8) (public1 : Slice Std.U8)
  (v : transport.Variant) (hash : H) :
 (run reservation d bytes proof public1 v hash).result=runRef reservation d bytes proof public1 v hash := by
 simp only [run,runRef,recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid,queryBlock,resumeBody]
 repeat' first
 | (intro hypothesis)
 | rfl
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid,queryBlock,resumeBody])
 | split
 | rfl
 all_goals simp_all only [recordRaw,recordK,recordE,recordSemantic,recordWeights,recordValidate,recordFilled,recordAny,recordDigest,NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_lift,NJU_Log.erase_liftM,NJU_Log.erase_pure,NJU_Log.erase_if,NJU_Log.erase_flow,NJU_Log.prod_cases,finishTail,queryEnd,queryMid,queryBlock,resumeBody]

#print axioms finishTail
#print axioms queryEnd
#print axioms queryMid
#print axioms queryBlock
#print axioms resumeBody
#print axioms header
end NJU_ResumeErase
