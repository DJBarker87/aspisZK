import NLW_064Invocation
set_option autoImplicit false
noncomputable section
namespace NLW_064Reference
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLW_064Invocation
/-- Allocator/ABI selections come from THIS entered child trace. No global
window, allocator-success Bool, reply dictionary or chosen second execution. -/
def commonRun (H : Bytes → State) (a : Args) (records : Records H) :=
 let f:=NLT_FrameFromCuts.frame records
 NJU_CommonObserved.run f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish f.finish) (NLT_RuntimeDigest.digest H)
  a.publicBytes a.proof a.checkpoint () none
def commonResult (H : Bytes → State) (a : Args) (records : Records H) :=
 let f:=NLT_FrameFromCuts.frame records
 NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish f.finish) (NLT_RuntimeDigest.digest H)
  a.publicBytes a.proof a.checkpoint () none
/-- Literal parse/?;mark(None,Parsed);common body with complete Result arms. -/
def transcription (H : Bytes → State) (a : Args) (records : Records H) : Result Reply :=
 match NLE_ParseInstall.parse a.proof with
 | .fail e=>.fail e
 | .div=>.div
 | .ok (.Err e)=>.ok (.Err e)
 | .ok (.Ok _)=>commonResult H a records
/-- Full child conclusions copied by STATEMENT from NLT_RowSpec, not by
re-proving its implementation. Native ? prefix/ordered internal effects,
allocator sites, C07 owned frames, full finish ABI and invalid arms are kept. -/
def CommonFacts (H : Bytes → State) (a : Args) (result : Result Reply) (records : Records H) : Prop :=
 result=commonResult H a records ∧
 records.map NLT_NativeInvocation.actual=(commonRun H a records).events ∧
 (∀ r∈records,NLT_NativeWindows.question (NLT_NativeInvocation.actual r)=NLT_NativeWindows.question r.entered) ∧
 (∀ r∈records,NLT_Root.CallLaw H r) ∧
 (∀ inside,NLT_Chronology.completed records=some inside →
  NLP_EffectOrder.expand (NLP_C04Chronology.atEvent H)
   (records.map NLT_NativeInvocation.actual)=inside)
def ChildFactsAtEntry (H : Bytes → State) (a : Args) (result : Result Reply) (records : Records H) : Prop :=
 match NLE_ParseInstall.parse a.proof with
 | .ok (.Ok _) => CommonFacts H a result records
 | _ => True
#print transcription
#print CommonFacts
end NLW_064Reference
