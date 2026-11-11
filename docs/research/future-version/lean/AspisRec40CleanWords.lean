import AspisRec40Frames
import AspisRec40CleanB

/-! Aspis 40-row clean event, word alignment: `extractor_word_alignment`, the
copy for the 40-row run of R1's `OraclePortCleanModel.extractor_word_alignment`
(the words the extractor rebuilds from the run are the words of the run's
proof). It is one of the pieces `AspisRec40Clean.accepted_facts` assembles.
Model level. (An earlier header here was a copy of `AspisRec40Clean`'s.) -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.CleanWords
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisR1 OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4
open RawCutProverCompiler (experiment)
open CanonicalCutEnrichedTranscript (Words enrichMessage)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

/-! ## Word alignment -/

private theorem proof_idempotent (w : Words) (pf : LiteralProtocol.Proof) :
    RawCutTranscriptRun.proof w (RawCutTranscriptRun.proof w pf) =
      RawCutTranscriptRun.proof w pf := by
  funext i
  cases h : pf i <;> simp [RawCutTranscriptRun.proof, enrichMessage, h]

/-- Copy of `OraclePortCleanModel.extractor_word_alignment`, with `AspisChecks`. -/
theorem extractor_word_alignment (D : LiteralByteProtocol.Decoder)
    (d : OracleDecisionFeasibilityCore.Decision) (P : RawCutProverCompiler.Prover)
    (H : Bytes → State)
    (checks : let run := eval H (AspisRec40.Decision.recorded D d P)
      AspisAcceptance.AspisChecks AspisOneTx.decodePairS run.2.1.1
        ((pr D).transcript H run.2.1.1 run.2.1.2 40).rounds) :
    let orig := eval H (experiment P (AspisRec40.Decision.verifier D d))
    let run := eval H (AspisRec40.Decision.recorded D d P)
    RawCutWordsFromRunExecutableBin.wordsFromRun run =
        BinCompiledRunWordStability.wordsFromRun D orig ∧
      RawCutTranscriptRun.proof (RawCutWordsFromRunExecutableBin.wordsFromRun run) run.2.1.2 =
        run.2.1.2 := by
  intro orig run
  have hpf : run.2.1.2 = RawCutTranscriptRun.proof
      (BinCompiledRunWordStability.wordsFromRun D orig) orig.2.1.2 := by
    change (eval H (AspisRec40.Decision.annotated D d (BinCompiledRunWordStability.wordsFromRun D) P)).2.1.2 = _
    rw [AspisRec40.Decision.annotated, AspisRec40.Decision.compiled_experiment_eval]
  have hvalidRun : RawCutWordsFromRunExecutableBin.ValidPrefix run := by
    intro j hj
    exact AspisRec40.CleanB.valid_of_checks D H run.2.1.1 run.2.1.2 checks j (by omega)
  have hw1 := RawCutWordsFromRunExecutableBin.wordsFromRun_eq_buildWords D run hvalidRun
  have hw2 : BinCompiledRunWordStability.wordsFromRun D run =
      BinCompiledRunWordStability.wordsFromRun D orig :=
    AspisRec40.Frames.wordsFromRun_compiled_eq_original D d P H
  have hwords := hw1.trans hw2
  refine ⟨hwords, ?_⟩
  rw [hwords, hpf]
  exact proof_idempotent _ _

#print axioms extractor_word_alignment

end AspisRec40.CleanWords
end
