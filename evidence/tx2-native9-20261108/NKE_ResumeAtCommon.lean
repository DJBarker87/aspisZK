import NKE_CommonCalls
import NKE_ResumeAssociation
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeAtCommon
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Install the concrete nested resume at C01 of THAT actual common log,
using the SAME Reservation. No independent child Result, log or allocation
success. Native reader/header/digest/allocator coverage remains separate. -/
theorem source (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (reply : R (verifier.Prepared × verifier.Accumulator))
 (entered : Event.resume ck proof pub reply∈
  (run wr rr merkle finish d pub proof ck hash none).events) :
 reply=NHT_ResultPort.action (NIL_StatePort.reply
  (NKE_Free.eval (NKE_ResumeProgram.run wr (NJC_ResumeCalls.digest d)
   ck proof pub .S2 hash)).result) := by
 have clause := NKE_CommonCalls.source wr rr merkle finish d pub proof ck hash
  (.resume ck proof pub reply) entered
 change reply=NJJ_Common.resume wr d ck proof pub .S2 hash at clause
 exact clause.trans (NKE_ResumeAssociation.at_common wr d ck proof pub hash).symm
#print source
#print axioms source
end NKE_ResumeAtCommon
