import FJt_NativeFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJt_NativeFinish
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
open AuS1_Finish
theorem forget {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State)) (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (c : Context)
    (new : Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c) :
    FIs_Finish.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c := by
  obtain ⟨s2,a0,a1,alphas,h0,h1,hs,r0,r1,weights,pair,dot,hw,hp,hd,e0,e1,ep,ed,rest⟩:=new
  refine ⟨s2,a0,a1,alphas,h0,h1,hs,r0,r1,weights,pair,dot,hw,hp,hd,e0,e1,ep,ed,?_⟩
  intro pairLaw matched equations
  apply rest pairLaw matched
  intro view claim polys opening claimRead polyRead
  have h:=equations view claim polys opening claimRead polyRead
  exact ⟨h.1,h.2.1⟩
#print axioms forget
end AspisR1.FJt_NativeFinish
end
