import NLP_ResumeInstall
import NLP_NativeMerkle
set_option autoImplicit false
noncomputable section
namespace NLP_NativeFold
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved NLB_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Both child implementations fixed. Auxiliary until SAME native allocator,
ABI/region interpretations and full nested-effect composition are installed.
There is no C01 packet or C04 Result-relation hypothesis. -/
theorem installed (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607)
 (observe : NKE_QueryInput.Args → QueryObservation)
 (cuts : QueryCuts wr rr fr (NLP_NativeMerkle.action H) d pub proof ck hash observe)
 (before : List Event) :
 let w:=flushWindow (queryWindow (window rr fr loc
  (NLB_ResumePacket.action NLP_ResumeInstall.native wr) (NLP_NativeMerkle.action H) d hash) observe)
 let p:=NKE_CommonProgram.run wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash none
 G w p before=.done (NJJ_Common.run wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash none)
  (before++(run wr rr (NLP_NativeMerkle.action H) (finish fr) d pub proof ck hash none).events) :=
 (NLB_Parent.native_fold wr rr fr loc NLP_ResumeInstall.native
  (NLP_NativeMerkle.action H) (NLP_NativeMerkle.action H) d pub proof ck hash
  (NLP_ResumeInstall.packet wr d ck proof pub hash)
  (fun _ _ _ _=>NLB_ErrorTransport.ReplyRel.same _) len observe cuts before).1
set_option pp.proofs false
#print installed
#print axioms installed
end NLP_NativeFold
