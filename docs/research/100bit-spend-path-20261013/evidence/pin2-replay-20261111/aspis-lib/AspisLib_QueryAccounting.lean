import AspisLib_Recorded
import RawCutCompilerDecoderStartLaw
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

set_option autoImplicit false
noncomputable section
namespace AspisR1.DecoderQueryAccounting
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open DecodedFirstReadUnionBound RawCutProverCompiler
open AspisR1.RecordedBinaryExperimentBin

variable {X M C I A Y : Type} [DecidableEq I]

theorem starts_le_queries (decoder : Dec X M C I A Y)
    (t : Table I A) (tr : List (I × A)) :
    decoderFirstReads decoder t tr ≤ tr.length := by
  induction tr generalizing t with
  | nil => rfl
  | cons q tr ih =>
    simp only [decoderFirstReads, List.length_cons]
    split <;> have := ih (put t q.1 q.2) <;> omega

def AdversaryQueries (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State, (eval H P).1.length ≤ Q

end AspisR1.DecoderQueryAccounting
