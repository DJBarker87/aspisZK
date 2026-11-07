import NLT_Interpreted
import NLT_Continuation
set_option autoImplicit false
noncomputable section
namespace NLT_ParentInvocation
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved NKE_Free
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- An interpreted invocation follows actual decoded replies. This remains an
auxiliary relation: Uninstalled is NOT an actual native parent frame. -/
def Interpreted (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (result : R Unit) (events : List Event) : Prop :=
 NLT_Continuation.Invocation (NLT_Interpreted.Local f H d hash)
  (NKE_CommonProgram.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
   d pub proof ck hash none) result events
/-- All entered local-cut inputs are consumed at their own occurrences. No
global observe function or QueryCuts family is a premise. The remaining
allocator/ABI provenance has not been discharged by placing it in f. -/
theorem source (f : NLT_Interpreted.Uninstalled) (H : Bytes → State)
 {X : Type} (d : aspis_core.digest.Digest32 X) (pub proof ck : Slice U8) (hash : X)
 (len : proof.val.length=57607) (result : R Unit) (events : List Event)
 (interpreted : Interpreted f H d pub proof ck hash result events) :
 result=NJJ_Common.run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none ∧
 events=(run f.resume f.pending (NLP_NativeMerkle.action H) (NLB_Parent.finish f.finish)
  d pub proof ck hash none).events := by
 have cuts : ∀ e∈(eval (NKE_CommonProgram.run f.resume f.pending (NLP_NativeMerkle.action H)
  (NLB_Parent.finish f.finish) d pub proof ck hash none)).events,
  ∀ actual,NLT_Interpreted.Local f H d hash e actual → actual=e := by
  rw [NKE_CommonEval.source]
  intro e entered actual localCut
  obtain ⟨input,same⟩:=localCut
  exact same.trans (NLT_Interpreted.step f H d pub proof ck hash len e entered input)
 have joined:=NLT_Continuation.source _ _ cuts result events interpreted
 rw [NKE_CommonEval.source,NJU_CommonObserved.source] at joined
 exact joined
set_option pp.proofs false
#print source
#print axioms source
end NLT_ParentInvocation
