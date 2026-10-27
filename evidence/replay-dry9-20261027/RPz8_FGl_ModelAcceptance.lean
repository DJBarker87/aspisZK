import RPz8_FGl_FinishContinuation
import RPz8_F3S_InputAtSecond
import RPz8_F3R_ModelSchedule
import RPz8_FGl_Finish
import F3S_FinishReached
import RPz7_AuS1_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_ModelAcceptance
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
theorem accepted {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State))
    (s2 : p.variant=.S2)
    (success : Port4D_FinishInstall.finish finish v p a none=ok (.Ok ()))
    (outcome : FGl_Finish.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace)
    (decoder : LiteralByteProtocol.Decoder) (modelInput : F3_Model.Input)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (input : SourceInputs) (modelView : LiteralOpeningView.View)
    (trEq : tr=LiteralTranscript.erasePrefix (AspisV8R19.MemoizedProgramLaw.eval H
      (F3J_SamplerRun.program modelInput.proof 0 33 (FS.emptyPrefix modelInput.semantic.value))).2)
    (wire : parsed.wire=bytesOf proof.val)
    (guard : OraclePortAdmission.Guard tr)
    (parser : OraclePortStoredParserC4.parseReached modelInput.stored tr=some parsed)
    (queries : OraclePortSelectedDraft.queries tr=some q)
    (found : OraclePortStoredDecisionDraftC4.input parsed q tr=some input)
    (opening : LiteralOpeningView.read (typedRows parsed q tr)=some modelView)
    (batch0 : (AspisV8R19.MemoizedProgramLaw.eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch0)).2=true)
    (batch1 : (AspisV8R19.MemoizedProgramLaw.eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch1)).2=true)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared tx1p)
      input.data q (SelectedChallengeMap.rhoOf input.rho))
    (saved : savedVec=Tx2N_Reader.writer H stored publicBytes
      (OraclePortCheckpointResumeC5.prepared (OraclePortAcceptedContextC6.context parsed input modelView)
        input.data (SelectedChallengeMap.rhoOf input.rho) q)
      (OraclePortCheckpointStateC3.write (model input.data (SelectedChallengeMap.rhoOf input.rho) q)).accumulator) :
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
,
        AuS1_Finish.Collision H trace parsed q ∨
        (AspisV8R19.MemoizedProgramLaw.eval H (F3_Model.verifier decoder modelInput)).2=true := by
  obtain ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd,cont⟩ :=
    FGl_FinishContinuation.reached finish v p a proof savedVec H stored publicBytes tx1p parsed trace
      s2 success outcome
  obtain ⟨parsedEq,matching,decoded⟩ := F3S_InputAtSecond.facts parsed q tr input (bytesOf proof.val) wire found queries
  refine ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd,?_⟩
  intro pairing matchesLaw semanticLaw dotLaw
  have result := cont parsed.semantic q tr input
    (by simpa only [←parsedEq] using found) queries
    (by simpa only [←parsedEq] using matching) decoded pairing matchesLaw
    (by simpa only [←parsedEq] using semanticLaw) dotLaw
    (OraclePortAcceptedContextC6.context parsed input modelView) prepare saved
  rcases result with collision | finishTrue
  · exact Or.inl collision
  · right
    have finishModel : OraclePortFrozen2.finish parsed q tr input (OraclePortFrozen2.completeState input q)=true := by
      simpa only [←parsedEq] using finishTrue
    have scheduler := F3R_ModelSchedule.complete decoder H modelInput parsed q input modelView
    rw [←trEq] at scheduler
    exact congrArg Prod.snd (scheduler guard parser queries found opening batch0 batch1 finishModel)
#print axioms accepted
end AspisR1.FGl_ModelAcceptance
end
