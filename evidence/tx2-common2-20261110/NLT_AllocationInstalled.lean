import NLT_NativeFacts
set_option autoImplicit false
noncomputable section
namespace NLT_AllocationInstalled
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Actual resume allocator selection is used by the full child G at those
SAME checkpoint/proof/public arguments, including all unentered/error prefixes. -/
def ResumeLaw {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X) :
 (e : Event) → NLT_NativeWindows.Input e → Prop
 | .resume ck proof pub _,r => NLB_ResumePacket.At NLP_ResumeInstall.native r d ck proof pub hash
 | _,_ => True
theorem resume (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X) (hash : X)
 (r : Occurrence H d hash) : ResumeLaw d hash r.entered r.input := by
 rcases r with ⟨e,input,detail⟩
 cases e <;> try exact True.intro
 exact NLP_ResumeInstall.packet input d _ _ _ hash
/-- C06's separate Reservation controls BOTH complete Result arms. The native
64-row family is retained as the successful branch's initialization law; it
is not claimed to execute on a reservation failure. -/
def PendingLaw : (e : Event) → NLT_NativeWindows.Input e → Prop
 | .pending weights _,r =>
   weights.val.length=64 ∧ NJJ_Common.pending r weights=NKE_CommonNative.pendingG r weights ∧
   (∀ pending,NKE_CommonNative.pendingG r weights=ok (.Ok pending) →
    pending.raw.val.length=64 ∧ pending.terms=0#usize) ∧
   ∀ i,i<64 → NJR_Cuts.pending weights
    (NKE_PendingNative.states weights (NKE_CommonNative.zeros weights) i)
    (NKE_PendingNative.states weights (NKE_CommonNative.zeros weights) (i+1)) i (i+1)
 | _,_ => True
theorem pending (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (r : Occurrence H d hash) (atRecord : r∈records) : PendingLaw r.entered r.input := by
 have entered:=NLT_NativeFacts.member H d pub proof ck hash len result records native r atRecord
 let f:=NLT_FrameFromCuts.frame records
 rcases r with ⟨e,input,detail⟩
 cases e <;> try exact True.intro
 case pending weights reply =>
  obtain ⟨width,_⟩:=NKE_CommonDomain.source f.resume f.pending (NLP_NativeMerkle.action H)
   (NLB_Parent.finish f.finish) d pub proof ck hash _ entered
  have exactReply:=NKE_PendingNative.source input weights (NKE_CommonNative.zeros weights) width
   (by simpa only [NKE_CommonNative.zeros,List.length_replicate] using width)
  have same : NJJ_Common.pending input weights=NKE_CommonNative.pendingG input weights := by
   cases input with
   | Err error => exact exactReply
   | Ok unit => cases unit;exact exactReply
  refine ⟨width,same,?_,?_⟩
  · intro pending returned
    have branch:=entered
    change Event.pending weights (NKE_CommonNative.pendingG input weights)∈_ at branch
    rw [returned] at branch
    exact NKO_C06.returned f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
     d pub proof ck hash weights pending branch
  · intro i inside
    exact NKE_PendingAtSource.native_rows f.resume f.pending (NLP_NativeMerkle.action H)
     (NLB_Parent.finish f.finish) d pub proof ck hash weights _ entered i inside
set_option pp.proofs false
#print resume
#print pending
#print axioms resume
#print axioms pending
end NLT_AllocationInstalled
