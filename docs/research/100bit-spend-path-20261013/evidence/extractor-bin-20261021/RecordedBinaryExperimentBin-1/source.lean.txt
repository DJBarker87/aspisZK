import R1FinalSoundness
import DecoderInstanceBoundaryBin
import RawRecordedOracleExtractionMassBin
import LiteralTableWordChoiceBin

set_option autoImplicit false
noncomputable section
namespace AspisR1.RecordedBinaryExperimentBin
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutProverCompiler RawCutTranscriptRun
open RawRecordedOracleExtractionMassBin DecoderInstanceBoundaryBin
abbrev SourceInputs := R1FinalSoundness.SourceInputs

abbrev original (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) := experiment P (verifier D d)
abbrev recorded (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) :=
  AcceptedAdaptiveFiatShamir.experiment
    (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (verifier D d)
abbrev dec := RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select LiteralTableWordChoiceBin.choose
abbrev binaryCollision (Q : Nat) (run : RunView) : Prop :=
  BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q run

/-- R16 instance/source-to-compiled-rows obligations, not a free terminal
Boolean. DECODER-INSTANCE-20261020 and HCHECKS-20261020 name the evidence still
needed from R14, frozen R15, R9, R-wire and S1–S10. -/
def InstanceFields (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (H : Bytes → State) (i : SourceInputs) : Prop :=
  SemanticPublicWire.parsePublic (compiledPublic D d P H).pubBytes = some i.decoded ∧
  (compiledRows D d P H)[31]? = some (i.m31,
    (TranscriptView.Value.queries (.ok i.queryBytes), i.state31)) ∧
  (compiledRows D d P H)[32]? = some (i.m32,
    (TranscriptView.Value.ordinary i.rho, i.state32)) ∧
  LiteralTranscript.valid 31 i.m31 ∧ LiteralTranscript.valid 32 i.m32

/-- R-wire binary completion: exactly LazyInj.decodes for the five-reader
binary collision event. BIN-COMMITMENT-MODEL §6 explicitly leaves this
consumer bridge open; WIRE-TX1/TX2 and R12/R13 must discharge it. -/
def BinaryCompletion (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State, ¬ binaryCollision Q (eval H (recorded D d P)) →
    FS2.accepts (eval H (recorded D d P)) →
    ∀ n a, n < (LiteralByteProtocol.protocol D).r →
      firstCell ((LiteralByteProtocol.protocol D).chain H
        (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 n) = some a →
      ∃ own pend g, dec a (tableBefore emptyTable (eval H (recorded D d P)).1 a) =
          some (own, pend, g) ∧
        bfollow g (traceFrom (eval H (recorded D d P)).1 a) own pend
          (tableBefore emptyTable (eval H (recorded D d P)).1 a) =
          some ((LiteralByteProtocol.protocol D).transcript H
              (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 n,
            (LiteralByteProtocol.protocol D).msg (eval H (recorded D d P)).2.1.2 n,
            (LiteralByteProtocol.protocol D).chal H
              (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 n)

/-- Binary R12/M7/M8 word alignment on the actual recorded extractor, including
failure-preserving decoding. R12-WORDS-20261020 and BIN-COMMITMENT-MODEL §6:
binary stability alone does not instantiate the old clean-model consumer. -/
def BinaryClean (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat) : Prop :=
  CleanAcceptedModel D (recorded D d P) (fun run => binaryCollision Q run ∨
    hitsChain3 dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)

/-- The deployed target's probability is an external carrier until R9/R20,
R10 and R16 give the source execution law. It must charge query-scan aborts
once. This is a probability transport obligation, not the target bound. -/
def DeployedTransport (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (deployedFailure : ℚ) : Prop :=
  deployedFailure ≤ lazyMean (recorded D d P) emptyTable failureMass +
    QueryScanModelFailure.failureProbability (2^18)

end AspisR1.RecordedBinaryExperimentBin
end
