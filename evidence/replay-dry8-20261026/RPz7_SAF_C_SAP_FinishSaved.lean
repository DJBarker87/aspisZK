/- New-prefix accepted-only consumer; source of origin: lean/SAP_FinishSaved.lean. -/
import RPz7_SAF_C_SAP_FinishConsumer
import RPz7_SAF_C_T2R_Finish
import RPz7_AuS1_Finish
import RPz7_SAF_C_Cons_Finish
import RPz7_T2R_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_C_SAP_FinishSaved
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
open AuS1_Finish
def Outcome {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State))
    (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (c : Context) : Prop :=
    p.variant = .S2 ∧ ∃ (alpha0 alpha1 : E) (alphas : Slice E),
    Array.index_usize p.alpha 0#usize = ok alpha0 ∧
    Array.index_usize p.alpha 1#usize = ok alpha1 ∧
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas ∧
    ∀     (r0 : RoundValues finish v.round0 alpha0 p.claim)
    (r1 : RoundValues finish v.round1 alpha1 r0.value)
    (weights : W) (pair dot : E)
    (hw : finish.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (hp : finish.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : finish.dot v.final_message a.weights.deref = ok (.Ok dot))
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release finish)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
,
    Collision H trace parsed q ∨
    (decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native finish) v p a none =
      ok (.Ok ())) = OraclePortFrozen2.finish (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide (Port4D_FinishInstall.finish finish v p a none = ok (.Ok ())) =
      D0TypedChecks.verify (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i ∧
    D0TypedChecks.verify (typedRows ⟨bytesOf proof.val,semantic⟩ q tr) i = true)

theorem consume {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State)) (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs) (c : Context)
    (old : SAF_C_SAP_FinishConsumer.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c)
    (saved : savedVec = Tx2N_Reader.writer H stored publicBytes
      (prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator) :
    Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace semantic q tr i c := by
  obtain ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,rest⟩ := old
  refine ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,?_⟩
  intro r0 r1 weights pair dot hw hp hd pairing matching semanticLaw dotLaw 
  exact rest r0 r1 weights pair dot hw hp hd pairing matching semanticLaw dotLaw saved

#print axioms consume
end AspisR1.SAF_C_SAP_FinishSaved
end
