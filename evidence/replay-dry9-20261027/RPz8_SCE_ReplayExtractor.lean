import RPz8_SCE_RecoveredExtraction
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_ReplayExtractor
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open CanonicalCutEnrichedTranscript SCE_ReplayFrames RawCutWordsFromRunExecutableBin

/-- The maintained extractor depends on semantic public bytes and recovered
words. The output does not depend on equality of chronological logs. -/
theorem extract_congr (left right : RawCutProverCompiler.RunView)
    (pub : left.2.1.1 = right.2.1.1)
    (words : wordsFromRun left = wordsFromRun right)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract left coins =
      RawRecordedPublicSpendExtractorBin.extract right coins := by
  have decoded : RawCutWordsFromRunPublicValidBin.runDecodedPublic left =
      RawCutWordsFromRunPublicValidBin.runDecodedPublic right :=
    congrArg (fun p : LiteralTranscript.Public => SemanticPublicWire.parsePublic p.pubBytes) pub
  have calls : (fun p => extractFromRun p left coins) = (fun p => extractFromRun p right coins) :=
    funext (fun p => SCE_RecoveredExtraction.extracted left right words p coins)
  exact congrArg₂ (fun p f => Option.bind p f) decoded calls

/-- Failure-mass transport retains the SAME acceptance flag and private coin
law; no failure probability or target bound is a hypothesis. -/
theorem mass_congr (left right : RawCutProverCompiler.RunView)
    (pub : left.2.1.1 = right.2.1.1)
    (words : wordsFromRun left = wordsFromRun right)
    (accept : left.2.2 = right.2.2) :
    RawRecordedOracleExtractionMassBin.failureMass left =
      RawRecordedOracleExtractionMassBin.failureMass right := by
  unfold RawRecordedOracleExtractionMassBin.failureMass
  apply congrArg AspisV8R19.OracleResampling.mean
  funext coins
  rw [accept,extract_congr left right pub words coins]

#print axioms extract_congr
#print axioms mass_congr
end AspisR1.SCE_ReplayExtractor
end
