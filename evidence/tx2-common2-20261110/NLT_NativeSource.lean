import NLT_ReseedTransport
import NLT_FrameFromCuts
import NLT_EraseCompatible
import NLT_QuestionStep
set_option autoImplicit false
noncomputable section
namespace NLT_NativeSource
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Literal parent continuation; these successful values seed source codecs
ONLY. Actual reservation failures are independently selected by the native
cut at each reached site and actually drive the continuation. -/
def skeleton (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) : Program Event (core.result.Result Unit verifier.Error) :=
 NKE_CommonProgram.run (.Ok ()) (.Ok ()) (NLP_NativeMerkle.action H) (NLB_Parent.finish (.Ok ()))
  d pub proof ck hash none
/-- No free wr/rr/fr/loc/observe/cuts parameter: every one is a concrete field
or a proved projection of the SAME detailed invocation. This is the semantic
forward fold; physical P6 adequacy is separately inventoried, never inferred
from this theorem's compilation. -/
theorem source (H : Bytes → State) {X : Type} (d : aspis_core.digest.Digest32 X)
 (pub proof ck : Slice U8) (hash : X) (len : proof.val.length=57607)
 (result : R Unit) (records : List (Occurrence H d hash))
 (native : Invocation H d hash (skeleton H d pub proof ck hash) result records) :
 let f:=NLT_FrameFromCuts.frame records
 result=NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none ∧
 records.map actual=(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events := by
 let f:=NLT_FrameFromCuts.frame records
 have ordered:=(NLT_NativeOrder.ordered _ result records native 0
  (NLT_SiteOrder.source (.Ok ()) (.Ok ()) (NLP_NativeMerkle.action H)
   (NLB_Parent.finish (.Ok ())) d pub proof ck hash)).2
 have compatible:=NLT_FrameFromCuts.compatible records ordered
 have reseed:=NLT_Reseed.source (.Ok ()) (.Ok ()) f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish (.Ok ())) (NLB_Parent.finish f.finish) d pub proof ck hash
 have replay:=NLT_ReseedTransport.forward _ _ reseed result records native
 have erased:=NLT_EraseCompatible.erase f _ result records replay compatible
 have cuts : ∀ e∈(eval (NKE_CommonProgram.run f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish f.finish) d pub proof ck hash none)).events,
  ∀ observed,NLT_EraseCompatible.Local f H d hash e observed → observed=e := by
  rw [NKE_CommonEval.source]
  intro e entered observed localCut
  obtain ⟨recorded,input,question,consistent,value⟩:=localCut
  exact value.trans (NLT_QuestionStep.source f H d pub proof ck hash len e entered
   recorded input question consistent)
 have joined:=NLT_Continuation.source _ _ cuts result _ erased
 rw [NKE_CommonEval.source,NJU_CommonObserved.source] at joined
 exact joined
set_option pp.proofs false
#print source
#print axioms source
end NLT_NativeSource
