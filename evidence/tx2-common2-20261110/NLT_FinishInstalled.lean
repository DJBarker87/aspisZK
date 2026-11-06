import NLT_NativeFacts
set_option autoImplicit false
noncomputable section
namespace NLT_FinishInstalled
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
def Law : (e : Event) → NLT_NativeWindows.Input e → Prop
 | .finish v p a _,input =>
   let execution:=NJF_FinishObserved.G input.1 input.2 v p a
   Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed input.1) v p a none=execution.1 ∧
   NIW_AlignFinishComposedLog.forget execution=NIW_AlignFinishExecution.run input.1 v p a ∧
   NIW_AlignFinishPrefix.Prefix execution.2.1
 | _,_ => True
/-- The SAME finish native input supplies both reservation and region/ABI
locations. The complete generalized child Result/history law is installed
internally; no raw-word canonicality or successful-finish premise is needed. -/
theorem installed (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (r : Occurrence H d hash) (atRecord : r∈records) : Law r.entered r.input := by
 have entered:=NLT_NativeFacts.member H d pub proof ck hash len result records native r atRecord
 let f:=NLT_FrameFromCuts.frame records
 rcases r with ⟨e,input,detail⟩
 cases e <;> try exact True.intro
 case finish v p a reply =>
  exact NKO_C09.child_at_actual f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
   d pub proof ck hash v p a _ entered input.1 input.2
set_option pp.proofs false
#print installed
#print axioms installed
end NLT_FinishInstalled
