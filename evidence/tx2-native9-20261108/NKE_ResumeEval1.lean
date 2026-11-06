import NKE_ResumeProgram1
import NKE_RunTactic
import NKE_FreeReplay
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeEval
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
theorem finishTailG  (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (queryValues : Array U32 22#usize) (r34 : verifier.Reader)  :
 NKE_Free.eval (NKE_ResumeProgram.finishTailG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues r34)=
 NJU_ResumeObserved.finishTailG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues r34 := by
 simp only [NKE_ResumeProgram.finishTailG,NJU_ResumeObserved.finishTailG,NKE_Free.eval_bind,NKE_Free.eval_record,NKE_Free.eval_liftM,NKE_Free.eval_pure,NKE_Free.eval_if,NKE_Free.eval_flow,NJU_Log.prod_cases,NKE_ResumeProgram.recordRaw,NJU_ResumeObserved.recordRaw,NKE_ResumeProgram.recordK,NJU_ResumeObserved.recordK,NKE_ResumeProgram.recordE,NJU_ResumeObserved.recordE,NKE_ResumeProgram.recordSemantic,NJU_ResumeObserved.recordSemantic,NKE_ResumeProgram.recordWeights,NJU_ResumeObserved.recordWeights,NKE_ResumeProgram.recordValidate,NJU_ResumeObserved.recordValidate,NKE_ResumeProgram.recordFilled,NJU_ResumeObserved.recordFilled,NKE_ResumeProgram.recordAny,NJU_ResumeObserved.recordAny,NKE_ResumeProgram.recordDigest,NJU_ResumeObserved.recordDigest,NKE_ResumeCodec.raw,NKE_ResumeCodec.k,NKE_ResumeCodec.e,NKE_ResumeCodec.semantic,NKE_ResumeCodec.weights,NKE_ResumeCodec.validate,NKE_ResumeCodec.filled,NKE_ResumeCodec.headerAny,NKE_ResumeCodec.digest]
 repeat' first
 | nke_run_bind
 | nke_intro
 | (fail_if_no_progress simp_all only [NKE_ResumeProgram.finishTailG,NJU_ResumeObserved.finishTailG,NKE_Free.eval_bind,NKE_Free.eval_record,NKE_Free.eval_liftM,NKE_Free.eval_pure,NKE_Free.eval_if,NKE_Free.eval_flow,NJU_Log.prod_cases,NKE_ResumeProgram.recordRaw,NJU_ResumeObserved.recordRaw,NKE_ResumeProgram.recordK,NJU_ResumeObserved.recordK,NKE_ResumeProgram.recordE,NJU_ResumeObserved.recordE,NKE_ResumeProgram.recordSemantic,NJU_ResumeObserved.recordSemantic,NKE_ResumeProgram.recordWeights,NJU_ResumeObserved.recordWeights,NKE_ResumeProgram.recordValidate,NJU_ResumeObserved.recordValidate,NKE_ResumeProgram.recordFilled,NJU_ResumeObserved.recordFilled,NKE_ResumeProgram.recordAny,NJU_ResumeObserved.recordAny,NKE_ResumeProgram.recordDigest,NJU_ResumeObserved.recordDigest,NKE_ResumeCodec.raw,NKE_ResumeCodec.k,NKE_ResumeCodec.e,NKE_ResumeCodec.semantic,NKE_ResumeCodec.weights,NKE_ResumeCodec.validate,NKE_ResumeCodec.filled,NKE_ResumeCodec.headerAny,NKE_ResumeCodec.digest])
 | split
#print axioms finishTailG
end NKE_ResumeEval
