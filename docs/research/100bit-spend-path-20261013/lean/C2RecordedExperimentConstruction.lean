import RawCutConstructedWords

/-!
Construct the C2 auxiliary word from the FULL recorded prover+verifier model
experiment. This is the second path of the accepted C2 source design. It is a
compiler component for the existing oracle-program model, not a claim that a
saved verifier-only counter supplies that experiment or that actual Rust
acceptance supplies the strict parser/constructor/budget/collision premises.
The source bridge and that complete witness are explicitly still required.
-/
set_option autoImplicit false
noncomputable section
namespace AspisR1.C2RecordedExperimentConstruction

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open CanonicalCutEnrichedTranscript RawCutTranscriptRun RawCutProverCompiler

/-- Recording is internal to the compiler and covers BOTH programs, in
chronological order. The constructor has no external oracle argument. -/
def compile (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) : Prover :=
  RawCutProverCompiler.compiled decoder d (RawCutWordsFromView.buildWords decoder) P

theorem row2_constructor (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (m : LiteralTranscript.BytesMessage) (previous : LiteralTranscript.C2Word)
    (h2 : (eval H (experiment P (verifier decoder d))).2.1.2 2 = .c2 m previous) :
    let v := eval H (experiment P (verifier decoder d))
    (eval H (compile decoder d P)).2.2 2 =
      .c2 m (RawCutWordsFromView.buildWords decoder v).c2 := by
  rw [compile, RawCutProverCompiler.eval_compiled]
  simp only [RawCutTranscriptRun.proof, h2, CanonicalCutEnrichedTranscript.enrichMessage]

/-- The finite view is obtained from the original complete experiment. Its
three selected frames are the actual model chain inputs at rounds0/2/30. -/
theorem word_from_actual_cuts (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    let v := eval H (experiment P (verifier decoder d))
    (RawCutWordsFromView.buildWords decoder v).c2 =
      TypedRecoveredWords.c2Value
        (rawC2Map v.1
          (RawCutWordsFromView.frame decoder H v.2.1.1 v.2.1.2 2)
          (RawCutWordsFromView.rootFrom 8
            (RawCutWordsFromView.frame decoder H v.2.1.1 v.2.1.2 2))) := by
  have h := RawCutWordsFromView.buildWords_eq_actual_cuts decoder d P H
  exact congrArg Words.c2 h

/-- Byte-based acceptance and the public statement are preserved by this
specific recorded-view constructor; no assertion about Rust acceptance. -/
theorem public_and_acceptance (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    let original := eval H (experiment P (verifier decoder d))
    let annotated := eval H (experiment (compile decoder d P) (verifier decoder d))
    annotated.2.1.1 = original.2.1.1 ∧ annotated.2.2 = original.2.2 :=
  RawCutProverCompiler.public_and_acceptance decoder d
    (RawCutWordsFromView.buildWords decoder) P H

/-- The query count is the complete model experiment's distinct first-read
budget. It is deliberately not instantiated by an on-chain call counter. -/
theorem firstReads_eq (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    firstReads emptyTable
      (eval H (experiment (compile decoder d P) (verifier decoder d))).1 =
    firstReads emptyTable (eval H (experiment P (verifier decoder d))).1 :=
  RawCutProverCompiler.firstReads_eq decoder d
    (RawCutWordsFromView.buildWords decoder) P H

#print axioms row2_constructor
#print axioms word_from_actual_cuts
#print axioms public_and_acceptance
#print axioms firstReads_eq
end AspisR1.C2RecordedExperimentConstruction
end
