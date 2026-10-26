import SAF_RoundUnique
import SAF_C_SAF_FinishPrepared
import SAP_FinishSaved
import SAP_FinishConsumer
import T2R_Finish
import AuS1_Finish
import Cons_Finish
import T2R_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_ForgetFinish
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
    (after : SAF_C_SAF_FinishPrepared.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c) :
    SAP_FinishSaved.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c := by
  obtain ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,r0,r1,weights,pair,dot,
    hw,hp,hd,e0,e1,ep,ed,rest⟩ := after
  refine ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,?_⟩
  intro r0' r1' weights' pair' dot' hw' hp' hd' pairing matched semanticLaw dotLaw canonical
  have er0 := SAF_RoundUnique.unique finish v.round0 alpha0 p.claim r0 r0'
  cases er0
  have er1 := SAF_RoundUnique.unique finish v.round1 alpha1 r0.value r1 r1'
  cases er1
  have ew : weights = weights' := core.result.Result.Ok.inj (Result.ok.inj (hw.symm.trans hw'))
  cases ew
  have epair : pair = pair' := core.result.Result.Ok.inj (Result.ok.inj (hp.symm.trans hp'))
  have edot : dot = dot' := core.result.Result.Ok.inj (Result.ok.inj (hd.symm.trans hd'))
  cases epair; cases edot
  exact rest ⟨pairing.round0,pairing.round1,pairing.pair⟩ matched semanticLaw dotLaw

#print axioms forget
end AspisR1.SAF_ForgetFinish
end
