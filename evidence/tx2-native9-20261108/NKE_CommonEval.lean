import NKE_CommonProgram
import NKE_RunTactic
import NKE_FreeReplay
set_option autoImplicit false
noncomputable section
namespace NKE_CommonEval
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NKE_Free.eval (NKE_CommonProgram.run wr rr merkle finish d pub proof ck hash none)=
 NJU_CommonObserved.run wr rr merkle finish d pub proof ck hash none := by
 simp only [NKE_CommonProgram.run,NJU_CommonObserved.run,NKE_Free.eval_bind,NKE_Free.eval_record,NKE_Free.eval_liftM,NKE_Free.eval_pure,NKE_Free.eval_if,NKE_Free.eval_flow,NJU_Log.prod_cases,NKE_CommonCodec.resume,NKE_CommonCodec.powers,NKE_CommonCodec.inactive,NKE_CommonCodec.merkle,NKE_CommonCodec.geometry,NKE_CommonCodec.pending,NKE_CommonCodec.query,NKE_CommonCodec.flush,NKE_CommonCodec.finish]
 repeat' first
 | nke_run_bind
 | nke_intro
 | (fail_if_no_progress simp_all only [NKE_CommonProgram.run,NJU_CommonObserved.run,NKE_Free.eval_bind,NKE_Free.eval_record,NKE_Free.eval_liftM,NKE_Free.eval_pure,NKE_Free.eval_if,NKE_Free.eval_flow,NJU_Log.prod_cases,NKE_CommonCodec.resume,NKE_CommonCodec.powers,NKE_CommonCodec.inactive,NKE_CommonCodec.merkle,NKE_CommonCodec.geometry,NKE_CommonCodec.pending,NKE_CommonCodec.query,NKE_CommonCodec.flush,NKE_CommonCodec.finish])
 | split
#print axioms source
end NKE_CommonEval
