import NLT_ParentInvocation
import NLT_Subcuts
set_option autoImplicit false
noncomputable section
namespace NLT_C04Installed
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Full typed obligation for each actual C04 subcut. It retains the complete
frozen Result and both native/adopted histories, or the two abort-prefix laws.
The record contains the native subcut, never these desired conclusions. -/
def Law (H : Bytes → State) : {e : Event} → NLT_Subcuts.Detail H e → Prop
 | _,.ordinary _ _ => True
 | _,.returning pr p folded reply inside out _ =>
   reply=NHT_ResultPort.action (ok out) ∧
   NLL_Parent.plan H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
    (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV=inside ∧
   NLL_ObservedCalls.calls H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
    (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV=
    (inside,NKV_ParentSource.observe (ok out)) ∧
   NLB_ErrorTransport.ReplyRel reply (NLP_C04Reply.lift (NKV_ParentSource.observe (ok out)))
 | _,.aborting pr p folded _ inside pending _ =>
   NLL_Prefix.At
    (NLL_Parent.plan H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
     (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV)
    (inside++pending.answered) pending.parts ∧
   NLL_Prefix.At
    (NLL_ObservedCalls.calls H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p)) p.queries 1#usize
     (NLL_Parent.sites (NLL_BatchSource.roots p folded)) NKV_ParentSource.zeroI NKV_ParentSource.zeroV).1
    (inside++pending.answered) pending.parts
/-- Each law is DISCHARGED from the CLOSED child at that exact entered event. -/
theorem at_event (H : Bytes → State) (wr rr : NP6_StdModel.Reservation) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0 : NLP_InputDomain.Root0 ck proof)
 (e : Event) (entered : e∈(run wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash none).events)
 (detail : NLT_Subcuts.Detail H e) : Law H detail := by
 cases detail with
 | ordinary e notMerkle => exact True.intro
 | returning pr p folded reply inside out child =>
   obtain ⟨replyLaw,historyLaw,observedLaw⟩:=NLP_C04Effects.returning H wr rr finish d pub proof ck hash
    len root0 pr p folded reply entered inside out child
   exact ⟨replyLaw,historyLaw,observedLaw,by rw [replyLaw];exact NLP_C04Reply.relation out⟩
 | aborting pr p folded error inside pending child =>
   exact NLP_C04Effects.aborting H wr rr finish d pub proof ck hash
    len root0 pr p folded (.fail error) entered inside pending child
/-- Installation on ONE detailed interpreted invocation. This is stronger than
assuming a separate C04 event log, but does not install physical allocator/ABI
provenance for f and is therefore NOT the TX2:065 root. -/
theorem installed (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0 : NLP_InputDomain.Root0 ck proof)
 (result : R Unit) (records : List (NLT_Subcuts.Occurrence f H d hash))
 (invocation : NLT_Subcuts.Invocation f H d hash
  (NKE_CommonProgram.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
   d pub proof ck hash none) result records) :
 ∀ record∈records,Law H record.detail := by
 have joined:=NLT_ParentInvocation.source f H d pub proof ck hash len result
  (records.map NLT_Subcuts.actual) (NLT_Subcuts.erase _ result records invocation)
 intro record member
 have entered : NLT_Subcuts.actual record∈(run f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish f.finish) d pub proof ck hash none).events := by
  rw [←joined.2]
  exact List.mem_map.mpr ⟨record,member,rfl⟩
 exact at_event H f.resume f.pending (NLB_Parent.finish f.finish) d pub proof ck hash len root0
  (NLT_Subcuts.actual record) entered record.detail
set_option pp.proofs false
#print at_event
#print installed
#print axioms at_event
#print axioms installed
end NLT_C04Installed
