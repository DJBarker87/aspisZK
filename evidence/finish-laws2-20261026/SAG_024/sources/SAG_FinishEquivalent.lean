import SAG_FinishPrepared
import SAF_C_SAF_FinishPrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_FinishEquivalent
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft
variable {W : Type}

theorem equivalent (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State)) (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : RecordedBinaryExperimentBin.SourceInputs)
    (c : OraclePortCheckpointResumeC5.Context) :
    SAG_FinishPrepared.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c ↔
    SAF_C_SAF_FinishPrepared.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c := by
  constructor
  · rintro ⟨s2,a0,a1,xs,h0,h1,hs,r0,r1,w,pair,dot,hw,hp,hd,e0,e1,ep,ed,rest⟩
    refine ⟨s2,a0,a1,xs,h0,h1,hs,r0,r1,w,pair,dot,hw,hp,hd,e0,e1,ep,ed,?_⟩
    intro laws matched semanticLaw dotLaw
    exact rest (SAG_Arithmetic.forget _ _ _ _ laws) matched semanticLaw dotLaw
  · rintro ⟨s2,a0,a1,xs,h0,h1,hs,r0,r1,w,pair,dot,hw,hp,hd,e0,e1,ep,ed,rest⟩
    refine ⟨s2,a0,a1,xs,h0,h1,hs,r0,r1,w,pair,dot,hw,hp,hd,e0,e1,ep,ed,?_⟩
    intro laws matched semanticLaw dotLaw
    exact rest (SAG_Arithmetic.reconstruct _ _ _ _ laws) matched semanticLaw dotLaw

#print axioms equivalent
end AspisR1.SAG_FinishEquivalent
end
