import NLT_C04NativeInstalled
set_option autoImplicit false
noncomputable section
namespace NLT_ReplyInstalled
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
def Law (H : Bytes → State) : {e : Event} → Detail H e → Prop
 | _,.returning pr p folded reply inside _ _ =>
   let observed:=NLL_ObservedCalls.calls H pr (NLP_RootCodec.parsed pr (Port3_BatchStage.root1 p))
    p.queries 1#usize (NLL_Parent.sites (NLL_BatchSource.roots p folded))
    NKV_ParentSource.zeroI NKV_ParentSource.zeroV
   observed.1=inside ∧ NLB_ErrorTransport.ReplyRel reply (NLP_C04Reply.lift observed.2)
 | _,_ => True
theorem at_event (H : Bytes → State) (wr rr : NP6_StdModel.Reservation) (finish : Finish)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (root0 : NLP_InputDomain.Root0 ck proof)
 (e : Event) (entered : e∈(run wr rr (NLP_NativeMerkle.action H) finish d pub proof ck hash none).events)
 (detail : Detail H e) : Law H detail := by
 cases detail with
 | ordinary e notMerkle => exact True.intro
 | returning pr p folded reply inside out child =>
   exact NLP_C04Reply.at_actual H wr rr finish d pub proof ck hash len root0
    pr p folded reply entered inside out child
 | aborting pr p folded error inside pending child => exact True.intro
theorem installed (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (root0 : NLP_InputDomain.Root0 ck proof) (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records) :
 ∀ record∈records,Law H record.detail := by
 intro record atRecord
 let f:=NLT_FrameFromCuts.frame records
 exact at_event H f.resume f.pending (NLB_Parent.finish f.finish) d pub proof ck hash len root0
  (actual record) (NLT_NativeFacts.member H d pub proof ck hash len result records native record atRecord) record.detail
set_option pp.proofs false
#print installed
#print axioms at_event
#print axioms installed
end NLT_ReplyInstalled
