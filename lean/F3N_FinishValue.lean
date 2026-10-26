import FinT_Model
import F3N_FinishLog
import T2Nat_FinishResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_FinishValue
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open scoped BigOperators
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open OraclePortStoredDecisionDraftC4 OraclePortCheckpointResumeC5
open RecordedBinaryExperimentBin (SourceInputs)
open RowFinish_Control
attribute [local instance] Classical.propDecidable
variable {W : Type}

theorem finish_value (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (before : SdkC_Source.Log) (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a saved : verifier.Accumulator) (alpha0 alpha1 : E)
    (r0 : RoundValues ops v.round0 alpha0 p.claim)
    (r1 : RoundValues ops v.round1 alpha1 r0.value)
    (weights : W) (alphas : Slice E) (pair dot : E)
    (s2 : p.variant = .S2)
    (ha0 : Array.index_usize p.alpha 0#usize = ok alpha0)
    (ha1 : Array.index_usize p.alpha 1#usize = ok alpha1)
    (hw : ops.newWeights p.variant p.semantic_alpha p.z = ok (.Ok weights))
    (has : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) p.alpha { «end» := 2#usize } = ok alphas)
    (hp : ops.pair weights alphas v.final_message p.kappa = ok (.Ok pair))
    (hd : ops.dot v.final_message a.weights.deref = ok (.Ok dot))
    (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (i : SourceInputs)
    (hi : input parsed q tr = some i) (hq : queries tr = some q)
    (read : LiteralMatchingData.read (typedRows parsed q tr) = some i.data)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (pairing_S3_S5_S9 : Port4D_Pairing.PairingLaws (Port3_FinishStage.release ops)
      CheckpointBytes5Output.ofE v p i.data)
    (matches_S4_S7 : ∀ j, MatchingSupport.match0 i.data (q j))
    (semantic_S3_S9 : R3SemanticRemainingJoins.EquationEndpoint i.decoded
      (typedRows parsed q tr) i.data)
    (dot_S5 : CheckpointBytes5Output.ofE dot = ∑ l : Fin 64, i.data.f l *
      LiteralOpeningView.eK ((CheckpointBytes5Output.accumulator a).weights l))
    (canonical_S3_S4_S5_S9 : ∀ x ∈ [r0.lhs,r0.rhs,r1.lhs,r1.rhs,pair,r1.value,dot,a.rhs],
      CheckpointBytes4ReaderFields.sourceE (CheckpointBytes5Output.ofE x) = x)
    (saved_ten : CheckpointBytes5Output.accumulator saved =
      (OraclePortCheckpointStateC3.write (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q)).accumulator)
    (twelve : CheckpointBytes5Output.accumulator a =
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model i.data
        (SelectedChallengeMap.rhoOf i.rho) q) 12 (CheckpointBytes5Output.accumulator saved)) :
    decide ((SdkC_Source.run hashv (T2Nat_Silent.code
      (T2Nat_FinishResult.installed ops v p a)) before).1=ok (.Ok ()))=
        OraclePortFrozen2.finish parsed q tr i (CheckpointBytes5Output.accumulator a) ∧
    decide ((SdkC_Source.run hashv (T2Nat_Silent.code
      (T2Nat_FinishResult.installed ops v p a)) before).1=ok (.Ok ()))=
        D0TypedChecks.verify (typedRows parsed q tr) i ∧
    (SdkC_Source.run hashv (T2Nat_Silent.code
      (T2Nat_FinishResult.installed ops v p a)) before).2=before := by
  have value := FinT_Model.finish_value ops v p a saved alpha0 alpha1 r0 r1 weights alphas pair dot
    s2 ha0 ha1 hw has hp hd parsed q tr i hi hq read decoded pairing_S3_S5_S9 matches_S4_S7
    semantic_S3_S9 dot_S5 canonical_S3_S4_S5_S9 saved_ten twelve
  rw [F3N_FinishLog.silent,T2Nat_FinishResult.installed_erase]
  have iff := Port3_QueryInstall.success_iff
    (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none) ()
  have installed : decide (Port4D_FinishInstall.finish ops v p a none=ok (.Ok ()))=
      decide (Port3_NativeFinishBody.verifier.finish_relation (Port4D_Round.native ops) v p a none=ok (.Ok ())) := by
    exact congrArg (fun P : Prop=>decide P) (propext iff)
  exact ⟨installed.trans value.1,value.2,rfl⟩

#print axioms finish_value
end AspisR1.F3N_FinishValue
end
