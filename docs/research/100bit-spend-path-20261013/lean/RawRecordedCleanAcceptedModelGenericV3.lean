import RawRecordedOracleExtractionMass

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawRecordedCleanAcceptedModelGeneric

open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.RawRecordedOracleExtractionMass
open AspisR1.LiteralAcceptanceTerminal
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.LiteralByteProtocol

/-- Package exact terminal Checks and raw no-hit facts as the model required by
recorded extractor averaging. Kept generic in the experiment so clients do not
need to unfold their adaptive run while elaborating the model type. -/
theorem cleanAcceptedModel_of_checks_and_nohit
    (decoder : LiteralByteProtocol.Decoder)
    (exp : RawRecordedOracleExtractionMass.Experiment)
    (hit : RawCutProverCompiler.RunView → Prop)
    (hchecks : ∀ H : Bytes → AspisV8R19.SourceDuplexStep.State,
      let run := eval H exp
      run.2.2 = true → Nonempty (LiteralAcceptanceTerminal.Checks run.2.1.1
        ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
          (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds))
    (hno : ∀ H : Bytes → AspisV8R19.SourceDuplexStep.State,
      let run := eval H exp
      run.2.2 = true → ¬ hit run →
        ¬ GenericNoHit.hitFrom LiteralClassifier.bad run.2.1.1 []
          ((LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
            (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds) :
    RawRecordedOracleExtractionMass.CleanAcceptedModel decoder exp hit := by
  intro H
  dsimp only [RawRecordedOracleExtractionMass.CleanAcceptedModel]
  change (eval H exp).2.2 = true → ¬ hit (eval H exp) → _
  intro ha hh
  obtain ⟨checks⟩ := hchecks H ha
  exact ⟨checks, hno H ha hh⟩

#print axioms cleanAcceptedModel_of_checks_and_nohit
end AspisR1.RawRecordedCleanAcceptedModelGeneric
end
