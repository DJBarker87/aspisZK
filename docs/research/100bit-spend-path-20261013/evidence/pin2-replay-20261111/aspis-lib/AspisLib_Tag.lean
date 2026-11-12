import AspisLib_Recorded
import RWireRawAdaptiveCompiledCompletion
import RWireCheckedFormat
import RWireInitialTag
import RawExtractorCostComposedV2
import HchecksReaderComposition
import Aeneas
import PublicCodecAgreement
import PublicRawCore
import PublicRawAmountGuard
import PublicRawAmountGuardAgreement
import R1PublicSourceBoundary
import R1PublicCodecAgreement
import R1SemanticPublicWireRoundTrip
import R1LiteralTranscript
import RawCutWordsFromView
import BinCombinedMerkleCollision
import QueryScanModelFailure
import R1FinalSoundnessNumeric
import BinCompiledRunWordStability
import RawRecordedOracleExtractionMassBin
import LiteralTableWordChoiceBin
import R19BudgetSamplerReads
import R1VerifierCallBudget
import QvStage2Count
import AspisV8R19.OracleFiniteSupport

set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialTagDecision
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun
open AspisR1.RecordedBinaryExperimentBin

theorem erased_transcript_tag (D : LiteralByteProtocol.Decoder)
    (H : Bytes → State) (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (n : Nat) :
    (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H pub pf n)).statement.tag =
      pub.tag := by
  change ((LiteralByteProtocol.protocol D).transcript H pub pf n).statement.tag = pub.tag
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end AspisR1.InitialTagDecision
