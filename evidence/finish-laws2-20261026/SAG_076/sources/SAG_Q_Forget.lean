import SAG_Q_Finish
import SAG_FinishPrepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_Q_Forget
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep OraclePortCompactDraft
variable {W : Type}

theorem forget (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State)) (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : RecordedBinaryExperimentBin.SourceInputs)
    (c : OraclePortCheckpointResumeC5.Context)
    (new : SAG_Q_Finish.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c) :
    SAG_FinishPrepared.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c := by
  obtain ⟨s2,a0,a1,xs,h0,h1,hs,r0,r1,w,pair,dot,hw,hp,hd,e0,e1,ep,ed,rest⟩ := new
  refine ⟨s2,a0,a1,xs,h0,h1,hs,r0,r1,w,pair,dot,hw,hp,hd,e0,e1,ep,ed,?_⟩
  intro laws matched semanticLaw dotLaw
  exact rest ⟨laws.boundary0,laws.eval0,laws.round1.boundary,laws.round1.eval,laws.pair⟩
    matched semanticLaw dotLaw

#print axioms forget
end AspisR1.SAG_Q_Forget
end
