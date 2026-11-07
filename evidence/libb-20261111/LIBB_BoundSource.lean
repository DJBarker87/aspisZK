import NLT_NativeSource
set_option autoImplicit false
noncomputable section
namespace LIBB_BoundSource
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLT_NativeInvocation
/-- Contextual representation transport. Compatibility is required ONLY on
reached records. This is not a new own-input domain or a completed library
field: integration must establish the runtime reservation/ABI binding. -/
theorem source (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (result : R Unit)
 (records : List (Occurrence H d hash))
 (native : Invocation H d hash (NLT_NativeSource.skeleton H d pub proof ck hash) result records)
 (bound : ∀ r∈records,NLT_NativeWindows.Compatible f r.entered r.input) :
 result=NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none ∧
 records.map actual=(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events := by
 have reseed:=NLT_Reseed.source (.Ok ()) (.Ok ()) f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish (.Ok ())) (NLB_Parent.finish f.finish) d pub proof ck hash
 have replay:=NLT_ReseedTransport.forward _ _ reseed result records native
 have erased:=NLT_EraseCompatible.erase f _ result records replay bound
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
#print axioms source
end LIBB_BoundSource
end
