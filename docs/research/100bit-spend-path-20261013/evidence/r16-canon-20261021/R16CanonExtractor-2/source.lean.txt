import R16CanonReduction
import RawRecordedOracleExtractionMassBin

/-! The maintained extractor factors through erased proof messages, public
statement and recorded log. It is not a function of the log alone: the
public and the commitment frames replayed from erased messages also enter. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R16CanonExtractor
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
open RawCommitmentFrameReplay

/-- Exact observational equality needed by the executable extractor. -/
structure Same (a b : RunView) : Prop where
  log : a.1 = b.1
  statement : a.2.1.1 = b.2.1.1
  erased : ∀ i, LiteralTranscript.erase (a.2.1.2 i) = LiteralTranscript.erase (b.2.1.2 i)

theorem frameAt_congr (pub : LiteralTranscript.Public) (state : State)
    (row : Nat) (a b : LiteralTranscript.Message)
    (same : LiteralTranscript.erase a = LiteralTranscript.erase b) :
    frameAt pub state row a = frameAt pub state row b := by
  cases row <;> cases a <;> cases b <;>
    simp_all [LiteralTranscript.erase, frameAt]

theorem successor_congr (H : Bytes → State) (pub : LiteralTranscript.Public)
    (state : State) (row : Nat) (a b : LiteralTranscript.Message)
    (same : LiteralTranscript.erase a = LiteralTranscript.erase b) :
    successor H pub state row a = successor H pub state row b := by
  cases row <;> cases a <;> cases b <;>
    simp_all [LiteralTranscript.erase, successor]

theorem stateBefore_congr (H : Bytes → State) (pub : LiteralTranscript.Public)
    (a b : LiteralProtocol.Proof)
    (same : ∀ i, LiteralTranscript.erase (a i) = LiteralTranscript.erase (b i))
    (n : Nat) : stateBefore H pub a n = stateBefore H pub b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stateBefore, ih]
    exact successor_congr H pub _ n _ _ (same n)

theorem frameFromView_congr (a b : RunView) (same : Same a b) (row : Nat) :
    frameFromView a row = frameFromView b row := by
  unfold frameFromView frame
  rw [same.log, same.statement, stateBefore_congr _ _ _ _ same.erased]
  exact frameAt_congr _ _ _ _ _ (same.erased row)

theorem words_congr (a b : RunView) (same : Same a b) :
    RawCutWordsFromRunExecutableBin.wordsFromRun a =
      RawCutWordsFromRunExecutableBin.wordsFromRun b := by
  unfold RawCutWordsFromRunExecutableBin.wordsFromRun
  rw [frameFromView_congr a b same 0, frameFromView_congr a b same 2,
      frameFromView_congr a b same 30, same.log]

theorem extract_congr (a b : RunView) (same : Same a b)
    (coins : GSConcreteByteDecoderBank.RawCoins) :
    RawRecordedPublicSpendExtractorBin.extract a coins =
      RawRecordedPublicSpendExtractorBin.extract b coins := by
  unfold RawRecordedPublicSpendExtractorBin.extract
    RawCutWordsFromRunPublicValidBin.runDecodedPublic
    RawCutWordsFromRunExecutableBin.extractFromRun
    RawCutWordsFromRunExecutableBin.initialWordsFromRun
    RawCutWordsFromRunExecutableBin.finalWordFromRun
  rw [same.statement, words_congr a b same]

theorem returned_relation_transfer (a b : RunView) (same : Same a b)
    (coins : GSConcreteByteDecoderBank.RawCoins) (w : SpendRelation.Wspend)
    (returned : RawRecordedPublicSpendExtractorBin.extract a coins = some w) :
    RawRecordedPublicSpendExtractorBin.extract b coins = some w ∧
      LiteralProtocol.relation b.2.1.1 w := by
  have hb := (extract_congr a b same coins).symm.trans returned
  exact ⟨hb, RawRecordedPublicSpendExtractorBin.returned_relation b coins w hb⟩

theorem failureMass_congr (a b : RunView) (same : Same a b)
    (accepted : a.2.2 = b.2.2) :
    RawRecordedOracleExtractionMassBin.failureMass a =
      RawRecordedOracleExtractionMassBin.failureMass b := by
  unfold RawRecordedOracleExtractionMassBin.failureMass
  congr 1
  funext coins
  rw [accepted, extract_congr a b same coins]

#print axioms frameAt_congr
#print axioms successor_congr
#print axioms stateBefore_congr
#print axioms frameFromView_congr
#print axioms words_congr
#print axioms extract_congr
#print axioms returned_relation_transfer
#print axioms failureMass_congr
end AspisR1.R16CanonExtractor
end
