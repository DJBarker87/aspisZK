import NNC_CommonWeak
import NLW_ReaderHeader
import NKE_ResumeDomain
set_option autoImplicit false
noncomputable section
namespace NNC_ResumeHeader
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Invert just the first native-model continuation. No Merkle law or Root0
is needed to show a returned parent passed its resume call. -/
theorem resume_of_ok (wr rr : NP6_StdModel.Reservation)
 (merkle : NJJ_Common.Merkle) (finish : NJJ_Common.Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (accepted : NJJ_Common.run wr rr merkle finish d pub proof ck hash none=ok (.Ok ())) :
 ∃ p a,NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) := by
 unfold NJJ_Common.run at accepted
 obtain ⟨reply,resumed,tail⟩:=OraclePortCkptAbiTry.bind_success _ _ _ accepted
 cases reply with
 | Err error =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame] at tail
   cases tail
 | Ok pair => exact ⟨pair.1,pair.2,resumed⟩
/-- The CLOSED resume byte comparison binds the actual checkpoint header to
its digest inputs, including the original partial runtime digest. -/
theorem header_of_resume (r : NP6_StdModel.Reservation) {X : Type}
 (d : aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H)
 (pub proof ck : Slice U8) (length : ck.val.length=1768)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (resumed : NJJ_Common.resume r d ck proof pub .S2 hash=ok (.Ok (p,a))) :
 NLW_ReaderHeader.decode (MultiproofConeCanonical.bytesOf ck.val)=
 some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) := by
 unfold NJJ_Common.resume at resumed
 rw [NJC_ResumeCalls.clause] at resumed
 have same:=NKE_ResumeDomain.action_ok _ _ resumed
 obtain ⟨calls⟩:=CheckpointBytes4Comparison.successful_calls (NJC_FilledClause.reserved r)
  (NJC_ResumeCalls.digest d) ck proof pub .S2 hash p a same
 exact NLW_ReaderHeader.calls (NJC_ResumeCalls.digest d) hash H oracle ck proof pub calls length
/-- Accepted native common invocation implies the header matched; only its
own extents and the existing returning-value oracle interpretation occur. -/
theorem native_ok (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X)
 (proofLength : proof.val.length=57607) (checkpointLength : ck.val.length=1768)
 (publicLength : pub.val.length≤1880)
 (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest d) hash H)
 (records : List (NLT_NativeInvocation.Occurrence H d hash))
 (native : NLT_CompleteRoot.Native H d pub proof ck hash (.resolved (ok (.Ok ())) records)) :
 NLW_ReaderHeader.decode (MultiproofConeCanonical.bytesOf ck.val)=
 some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) := by
 have weak:=(NNC_CommonWeak.root H d pub proof ck hash proofLength publicLength).1 _ native
 obtain ⟨p,a,resumed⟩:=resume_of_ok _ _ _ _ d pub proof ck hash weak.1.symm
 exact header_of_resume _ d hash H oracle pub proof ck checkpointLength p a resumed
#print resume_of_ok
#print header_of_resume
#print native_ok
#print axioms resume_of_ok
#print axioms header_of_resume
#print axioms native_ok
end NNC_ResumeHeader
