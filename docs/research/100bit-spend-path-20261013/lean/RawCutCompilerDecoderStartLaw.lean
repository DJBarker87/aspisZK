import DecodedFirstReadReplay

/-! Lossless transport of the actual decoder-start count through the raw
recording/enrichment compiler. This does not supply a numerical start bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawCutCompilerDecoderStartLaw
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RawCutProverCompiler RawCutTranscriptRun CanonicalCutEnrichedTranscript
open DecodedFirstReadUnionBound

variable {Y : Type}

/-- All decoder-start opportunities are preserved exactly, even when the
statement and proof are chosen adaptively. The replayed external verifier
reads only cells already read in the recorded original experiment. -/
theorem decoderStarts_eq
    (dec : Dec LiteralTranscript.Public LiteralTranscript.Message
      LiteralTranscript.Challenge Bytes State Y)
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    decoderFirstReads dec emptyTable
      (eval H (experiment (compiled decoder d buildWords P) (verifier decoder d))).1 =
    decoderFirstReads dec emptyTable
      (eval H (experiment P (verifier decoder d))).1 := by
  rw [compiled_experiment_eval]
  rw [RawCutProverCompiler.experiment_eval]
  exact decoderFirstReads_repeat_suffix dec _ _

theorem decoderStart_bound_preserved
    (dec : Dec LiteralTranscript.Public LiteralTranscript.Message
      LiteralTranscript.Challenge Bytes State Y)
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool)
    (buildWords : RunView → Words) (P : Prover) (N : Nat)
    (hN : ∀ H : Bytes → State, decoderFirstReads dec emptyTable
      (eval H (experiment P (verifier decoder d))).1 ≤ N) :
    ∀ H : Bytes → State, decoderFirstReads dec emptyTable
      (eval H (experiment (compiled decoder d buildWords P) (verifier decoder d))).1 ≤ N := by
  intro H
  rw [decoderStarts_eq dec decoder d buildWords P H]
  exact hN H

#print axioms decoderStarts_eq
#print axioms decoderStart_bound_preserved
end AspisR1.RawCutCompilerDecoderStartLaw
end
