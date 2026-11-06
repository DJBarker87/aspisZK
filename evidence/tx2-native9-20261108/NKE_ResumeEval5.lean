import NKE_ResumeProgram5
import NKE_RunTactic
import NKE_ResumeEval4
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeEval
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
theorem resumeBodyG  (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)  :
 NKE_Free.eval (NKE_ResumeProgram.resumeBodyG reservation d bytes v i4 end1)=
 NJU_ResumeObserved.resumeBodyG reservation d bytes v i4 end1 := by
 simp only [NKE_ResumeProgram.resumeBodyG,NJU_ResumeObserved.resumeBodyG,NKE_Free.eval_bind,NKE_Free.eval_record,NKE_Free.eval_liftM,NKE_Free.eval_pure,NKE_Free.eval_if,NKE_Free.eval_flow,NJU_Log.prod_cases,NKE_ResumeProgram.recordRaw,NJU_ResumeObserved.recordRaw,NKE_ResumeProgram.recordK,NJU_ResumeObserved.recordK,NKE_ResumeProgram.recordE,NJU_ResumeObserved.recordE,NKE_ResumeProgram.recordSemantic,NJU_ResumeObserved.recordSemantic,NKE_ResumeProgram.recordWeights,NJU_ResumeObserved.recordWeights,NKE_ResumeProgram.recordValidate,NJU_ResumeObserved.recordValidate,NKE_ResumeProgram.recordFilled,NJU_ResumeObserved.recordFilled,NKE_ResumeProgram.recordAny,NJU_ResumeObserved.recordAny,NKE_ResumeProgram.recordDigest,NJU_ResumeObserved.recordDigest,NKE_ResumeCodec.raw,NKE_ResumeCodec.k,NKE_ResumeCodec.e,NKE_ResumeCodec.semantic,NKE_ResumeCodec.weights,NKE_ResumeCodec.validate,NKE_ResumeCodec.filled,NKE_ResumeCodec.headerAny,NKE_ResumeCodec.digest,NKE_ResumeEval.finishTailG,NKE_ResumeEval.queryEndG,NKE_ResumeEval.queryMidG,NKE_ResumeEval.queryBlockG]
 repeat' first
 | nke_run_bind
 | nke_intro
 | (fail_if_no_progress simp_all only [NKE_ResumeProgram.resumeBodyG,NJU_ResumeObserved.resumeBodyG,NKE_Free.eval_bind,NKE_Free.eval_record,NKE_Free.eval_liftM,NKE_Free.eval_pure,NKE_Free.eval_if,NKE_Free.eval_flow,NJU_Log.prod_cases,NKE_ResumeProgram.recordRaw,NJU_ResumeObserved.recordRaw,NKE_ResumeProgram.recordK,NJU_ResumeObserved.recordK,NKE_ResumeProgram.recordE,NJU_ResumeObserved.recordE,NKE_ResumeProgram.recordSemantic,NJU_ResumeObserved.recordSemantic,NKE_ResumeProgram.recordWeights,NJU_ResumeObserved.recordWeights,NKE_ResumeProgram.recordValidate,NJU_ResumeObserved.recordValidate,NKE_ResumeProgram.recordFilled,NJU_ResumeObserved.recordFilled,NKE_ResumeProgram.recordAny,NJU_ResumeObserved.recordAny,NKE_ResumeProgram.recordDigest,NJU_ResumeObserved.recordDigest,NKE_ResumeCodec.raw,NKE_ResumeCodec.k,NKE_ResumeCodec.e,NKE_ResumeCodec.semantic,NKE_ResumeCodec.weights,NKE_ResumeCodec.validate,NKE_ResumeCodec.filled,NKE_ResumeCodec.headerAny,NKE_ResumeCodec.digest,NKE_ResumeEval.finishTailG,NKE_ResumeEval.queryEndG,NKE_ResumeEval.queryMidG,NKE_ResumeEval.queryBlockG])
 | split
#print axioms resumeBodyG
end NKE_ResumeEval
