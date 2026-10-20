import BinCompiledRunWordStability
import LiteralTableWordChoiceBin
import RawCutWordsFromView
import RawCutProverCompiler

/-! The compiler's actual public/proof output has the enriched transcript and
unchanged first-read frame and challenge. These equalities connect decoder
completion to the protocol's actual compiled-prover transcript. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCompiledTranscript
open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open CanonicalCutEnrichedTranscript

def original (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) :=
  eval H (RawCutProverCompiler.experiment prover (RawCutProverCompiler.verifier decoder d))

def output (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) :=
  (eval H (RawCutProverCompiler.compiled decoder d (BinCompiledRunWordStability.wordsFromRun decoder) prover)).2

theorem output_eq (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) :
    output decoder d prover H =
      ((original decoder d prover H).2.1.1,
        RawCutTranscriptRun.proof (BinCompiledRunWordStability.wordsFromRun decoder (original decoder d prover H))
          (original decoder d prover H).2.1.2) := by
  unfold output
  rw [RawCutProverCompiler.eval_compiled]
  rfl

theorem transcript (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) (n : Nat) :
    (LiteralByteProtocol.protocol decoder).transcript H
      (output decoder d prover H).1 (output decoder d prover H).2 n =
    enrichPrefix (BinCompiledRunWordStability.wordsFromRun decoder (original decoder d prover H))
      ((LiteralByteProtocol.protocol decoder).transcript H
        (original decoder d prover H).2.1.1 (original decoder d prover H).2.1.2 n) := by
  rw [output_eq]
  exact RawCutTranscriptRun.transcript_eq ..

theorem chain (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) (n : Nat) :
    (LiteralByteProtocol.protocol decoder).chain H
      (output decoder d prover H).1 (output decoder d prover H).2 n =
    (LiteralByteProtocol.protocol decoder).chain H
      (original decoder d prover H).2.1.1 (original decoder d prover H).2.1.2 n := by
  rw [output_eq]
  exact RawCutTranscriptRun.chain_eq ..

theorem challenge (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) (n : Nat) :
    (LiteralByteProtocol.protocol decoder).chal H
      (output decoder d prover H).1 (output decoder d prover H).2 n =
    (LiteralByteProtocol.protocol decoder).chal H
      (original decoder d prover H).2.1.1 (original decoder d prover H).2.1.2 n := by
  exact congrArg (fun s => (eval H s.toProgram).2) (chain decoder d prover H n)

theorem frame (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : RawCutProverCompiler.Prover) (H : Bytes → State) (n : Nat) :
    RawCutWordsFromView.frame decoder H (output decoder d prover H).1 (output decoder d prover H).2 n =
    RawCutWordsFromView.frame decoder H
      (original decoder d prover H).2.1.1 (original decoder d prover H).2.1.2 n := by
  unfold RawCutWordsFromView.frame
  rw [chain]

#print axioms transcript
#print axioms chain
#print axioms challenge
#print axioms frame
#print axioms output_eq
end AspisR1.RWireRawCompiledTranscript
end
