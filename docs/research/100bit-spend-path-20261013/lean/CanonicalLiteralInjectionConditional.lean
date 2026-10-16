import CanonicalLiteralProof
import RawAdaptiveDecoderInjection
import RawCutProverCompiler

/-! Formatting specialization for the decoded-wire front end. Literal row
constructors and public tag are supplied by `CanonicalLiteralProof`; only the
two strict row payload decoders remain as explicit parser obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CanonicalLiteralInjection

open FS FS2 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State
abbrev WireProof := CanonicalLiteralProof.WireProof
abbrev DecodedInput := CanonicalLiteralProof.DecodedInput

/-- Exactly the strict parser successes required by the current
`CommitmentMessages` interface. This does not assert that arbitrary byte
messages have the corresponding constructor. -/
def StrictRows (wire : WireProof) : Prop :=
  (∃ r2 : State,
    SemanticRecordCodec.decode ⟨2, by decide⟩ (wire.2 2).val =
      some ⟨.c2Root r2, by rfl⟩) ∧
  (∃ v30 : OpeningRecordCodec.Payload .second,
    OpeningRecordCodec.decode .second (wire.2 30).val = some v30)

/-- The canonical row constructor choices turn strict row parser successes
into the exact commitment-message package consumed by decoder injection. -/
theorem commitmentMessages_of_strictRows (wire : WireProof)
    (hstrict : StrictRows wire) :
    RawAdaptiveDecoderInjection.CommitmentMessages
      (CanonicalLiteralProof.literalProof wire) := by
  rcases hstrict with ⟨⟨r2, h2⟩, ⟨v30, h30⟩⟩
  refine ⟨wire.1, CanonicalLiteralProof.zeroC1, wire.2 2,
    CanonicalLiteralProof.zeroC2, r2, wire.2 30,
    CanonicalLiteralProof.zeroV, v30, ?_, ?_, ?_, h2, h30⟩
  · simp [CanonicalLiteralProof.literalProof, CanonicalLiteralProof.literalMessage]
  · simp [CanonicalLiteralProof.literalProof, CanonicalLiteralProof.literalMessage]
  · simp [CanonicalLiteralProof.literalProof, CanonicalLiteralProof.literalMessage]

/-- Name for the concrete decoded-wire prover used by the injection theorem. -/
def LiteralProver (P : Program Bytes State DecodedInput) :
    RawCutProverCompiler.Prover := CanonicalLiteralProof.liftProver P

/-- The output selected by the adaptive experiment is exactly the canonical
public/proof pair produced by the lifted prover. -/
theorem experiment_output (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Program Bytes State DecodedInput) (H : Bytes → State) :
    (eval H (RawCutProverCompiler.experiment (LiteralProver P)
      (RawCutProverCompiler.verifier decoder d))).2.1 =
      CanonicalLiteralProof.outputOf (eval H P).2 := by
  unfold LiteralProver
  rw [RawCutProverCompiler.experiment_eval, CanonicalLiteralProof.eval_liftProver]

/-- For a decoded-wire prover whose two commitment payloads pass their strict
row parsers, the `hformat` obligation of `RawAdaptiveDecoderInjection.injection`
is automatic: validity and tag follow from construction. The acceptance
antecedent is retained to match that API, but no arbitrary byte-based decision
is claimed to validate constructors. -/
theorem hformat_of_decodedWire
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Program Bytes State DecodedInput)
    (hstrict : ∀ H : Bytes → State,
      FS2.accepts (eval H (RawCutProverCompiler.experiment (LiteralProver P)
        (RawCutProverCompiler.verifier decoder d))) →
      StrictRows ((eval H P).2.wire)) :
    ∀ H : Bytes → State,
      FS2.accepts (eval H (RawCutProverCompiler.experiment (LiteralProver P)
        (RawCutProverCompiler.verifier decoder d))) →
      let run := eval H (RawCutProverCompiler.experiment (LiteralProver P)
        (RawCutProverCompiler.verifier decoder d))
      (∀ i < 33, LiteralTranscript.valid i (run.2.1.2 i)) ∧
        run.2.1.1.tag = 2 ∧
        RawAdaptiveDecoderInjection.CommitmentMessages run.2.1.2 := by
  intro H hacc
  have hv := CanonicalLiteralProof.outputOf_valid ((eval H P).2)
  have htag := CanonicalLiteralProof.outputOf_public_tag2 ((eval H P).2)
  have hm := commitmentMessages_of_strictRows ((eval H P).2).wire (hstrict H hacc)
  simpa only [experiment_output] using ⟨hv, htag, hm⟩

#print axioms commitmentMessages_of_strictRows
#print axioms experiment_output
#print axioms hformat_of_decodedWire

end AspisR1.CanonicalLiteralInjection
end
