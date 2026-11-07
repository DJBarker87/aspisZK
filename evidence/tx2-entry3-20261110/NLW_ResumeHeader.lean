import NLW_ReaderHeader
import NLP_ResumeRoots
set_option autoImplicit false
noncomputable section
namespace NLW_ResumeHeader
open Aeneas Aeneas.Std AspisR1 VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Lift concrete resume comparison records at the actually reached source
 invocation. This requires only the existing per-call hash realization law;
 it does not assume total digest execution or equal proof buffers. -/
theorem returned (reservation : NP6_StdModel.Reservation) {X : Type}
 (d : aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
 (oracle : CheckpointBytes5Inputs.Oracle (NJC_ResumeCalls.digest d) hash H)
 (ck proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash=.ok (.Ok (p,a))) :
 NLW_ReaderHeader.decode (MultiproofConeCanonical.bytesOf ck.val)=
  some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) := by
 have size:=NKE_ResumeWidth.checkpoint reservation d ck proof pub hash p a entered
 unfold NJJ_Common.resume at entered
 rw [NJC_ResumeCalls.clause] at entered
 have same:=NKE_ResumeDomain.action_ok _ _ entered
 change AspisR1Stage2.verifier.resumeWithOps
  (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation))
  (NJC_ResumeCalls.digest d) ck proof pub .S2 hash=.ok (.Ok (p,a)) at same
 obtain ⟨calls⟩:=CheckpointBytes4Comparison.successful_calls
  (NJC_FilledClause.reserved reservation) (NJC_ResumeCalls.digest d)
  ck proof pub .S2 hash p a same
 exact NLW_ReaderHeader.calls (NJC_ResumeCalls.digest d) hash H oracle ck proof pub calls size
#print returned
#print axioms returned
end NLW_ResumeHeader
