import RPz8_FGl_Finish
import F3S_FinishReached
import RPz7_AuS1_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_FinishContinuation
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
theorem reached {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (savedVec : alloc.vec.Vec U8)
    (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State))
    (s2 : p.variant=.S2)
    (success : Port4D_FinishInstall.finish finish v p a none=ok (.Ok ()))
    (outcome : FGl_Finish.Outcome finish v p a proof savedVec H stored publicBytes tx1p parsed trace) :
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
      ∀    (semantic : List Bytes) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (hi : input (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr = some i) (hq : queries tr = some q)
    (read : LiteralMatchingData.read (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release finish)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr) i.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (c : Context)
    (prepare_S1 : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared tx1p)
      i.data q (SelectedChallengeMap.rhoOf i.rho))
    (tx1_saved : savedVec = Tx2N_Reader.writer H stored publicBytes
      (prepared c i.data (SelectedChallengeMap.rhoOf i.rho) q)
      (OraclePortCheckpointStateC3.write (model i.data (SelectedChallengeMap.rhoOf i.rho) q)).accumulator),
    AuS1_Finish.Collision H trace parsed q ∨
      OraclePortFrozen2.finish (⟨bytesOf proof.val,semantic⟩ : Parsed) q tr i
        (OraclePortFrozen2.completeState i q)=true := by
  obtain ⟨alpha0,alpha1,value0,value1,weights,alphas,pair,dot,ha0,ha1,h0,h1,hw,has,hp,hd⟩ :=
    F3S_FinishReached.reached finish v p a s2 success
  obtain ⟨r0,er0⟩ := F3S_RoundValues.reached finish v.round0 alpha0 p.claim 0#usize value0 h0
  subst value0
  obtain ⟨r1,er1⟩ := F3S_RoundValues.reached finish v.round1 alpha1 r0.value 1#usize value1 h1
  refine ⟨alpha0,alpha1,r0,r1,weights,alphas,pair,dot,ha0,ha1,hw,has,hp,hd,?_⟩
  intro semantic q tr i hi hq read decoded pairing matchesLaw semanticLaw dotLaw c prepare tx1_saved
  rcases outcome alpha0 alpha1 r0 r1 weights alphas pair dot s2 ha0 ha1 hw has hp hd
    semantic q tr i hi hq read decoded pairing matchesLaw semanticLaw dotLaw c prepare tx1_saved with
    collision | checked
  · exact Or.inl collision
  · exact Or.inr checked.2.2.2
#print axioms reached
end AspisR1.FGl_FinishContinuation
end
