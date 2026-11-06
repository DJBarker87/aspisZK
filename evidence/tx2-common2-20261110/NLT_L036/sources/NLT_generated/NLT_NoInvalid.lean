import NLT_NativeSource
import NLT_InvalidTransport
set_option autoImplicit false
noncomputable section
namespace NLT_NoInvalid
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
theorem source (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (records : List (Occurrence H d hash))
 (bad : NLT_NativeInvocation.Invalid H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) records) : False := by
 let f:=NLT_FrameFromCuts.frame records
 have ordered:=(NLT_InvalidTransport.ordered _ records bad 0
  (NLT_SiteOrder.source (.Ok ()) (.Ok ()) (NLP_NativeMerkle.action H)
   (NLB_Parent.finish (.Ok ())) d pub proof ck hash)).2
 have compatible:=NLT_FrameFromCuts.compatible records ordered
 have same:=NLT_Reseed.source (.Ok ()) (.Ok ()) f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish (.Ok ())) (NLB_Parent.finish f.finish) d pub proof ck hash
 have replay:=NLT_InvalidTransport.reseed _ _ same records bad
 have erased:=NLT_InvalidTransport.erase f _ records replay compatible
 have cuts : ∀ e∈(eval (NKE_CommonProgram.run f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish f.finish) d pub proof ck hash none)).events,
  ∀ observed,NLT_EraseCompatible.Local f H d hash e observed → observed=e := by
  rw [NKE_CommonEval.source]
  intro e entered observed localCut
  obtain ⟨recorded,input,question,consistent,value⟩:=localCut
  exact value.trans (NLT_QuestionStep.source f H d pub proof ck hash len e entered
   recorded input question consistent)
 exact NLT_Continuation.no_invalid _ _ cuts _ erased
set_option pp.proofs false
#print source
#print axioms source
end NLT_NoInvalid
