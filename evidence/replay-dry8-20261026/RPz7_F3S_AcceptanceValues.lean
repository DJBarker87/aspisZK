import RPz7_F3S_ModelAcceptance
import RPz7_F3S_FinishContinuation
import RPz7_F3S_InputAtSecond
import RPz7_F3R_ModelSchedule
import RPz7_F3R_Finish
import F3S_FinishReached
import RPz7_AuS1_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_AcceptanceValues
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
open AuS1_Finish
/-- Strong finish continuation indexed by the SAME source TX2 witnesses. -/
def Values {W : Type} (finish : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (H : Bytes → State) (trace : List (Bytes × State))
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : SourceInputs) (decoder : LiteralByteProtocol.Decoder) (modelInput : F3_Model.Input) : Prop :=

    ∃ (alpha0 alpha1 : E)
      (r0 : RoundValues finish v.round0 alpha0 p.claim)
      (r1 : RoundValues finish v.round1 alpha1 r0.value)
      (weights : W) (alphas : Slice E) (pair dot : E),
      Array.index_usize p.alpha 0#usize=ok alpha0 ∧
      Array.index_usize p.alpha 1#usize=ok alpha1 ∧
      finish.newWeights p.variant p.semantic_alpha p.z=ok (.Ok weights) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha {«end»:=2#usize}=ok alphas ∧
      finish.pair weights alphas v.final_message p.kappa=ok (.Ok pair) ∧
      finish.dot v.final_message a.weights.deref=ok (.Ok dot) ∧
      ∀    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release finish)
      CheckpointBytes5Output.ofE v p input.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 input.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint input.decoded
      (typedRows parsed q tr) input.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, input.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (canonical_S3_S4_S5_S9 : ∀ x ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs],
      CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE x) = x)
,
        AuS1_Finish.Collision H trace parsed q ∨
        (AspisV8R19.MemoizedProgramLaw.eval H (F3_Model.verifier decoder modelInput)).2=true
end AspisR1.F3S_AcceptanceValues
end
