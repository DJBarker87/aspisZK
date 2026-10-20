import RawChecksInjectionFormat

/-! R18 tag discharge for runs mapped to the selected deployed public.
The source-to-public mapping remains explicit, as required by the free public
carrier in the model. Commitment formats do not constrain digest values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawDeployedTranscriptFormat
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open RawCutProverCompiler RawCutTranscriptRun

theorem mapped_public_tag (run : (Bytes → State) → RunView)
    (pubBytes : List SemanticPublicWire.Byte)
    (pub : R0P.Public SemanticPublicWire.M31)
    (hparse : SemanticPublicWire.parsePublic pubBytes = some pub)
    (hpublic : ∀ H, (run H).2.1.1 =
      SelectedTranscriptParams.publicStatement pubBytes pub hparse) :
    ∀ H, (run H).2.1.1.tag = 2 := by
  intro H
  rw [hpublic H]
  exact SelectedTranscriptParams.publicStatement_tag pubBytes pub hparse

/-- Discharges htag and the constructor/parser format interface together.
Checks and both experiment equations remain the same hypotheses as the
existing injection theorem; binary Merkle acceptance is a separate layer. -/
theorem mapped_checks_format
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State)
    (original annotated : RunView)
    (horiginal : original = eval H (experiment P (verifier decoder d)))
    (hannotated : annotated = eval H (experiment
      (compiled decoder d (RawCutWordsFromView.buildWords decoder) P) (verifier decoder d)))
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (hrows : rs = ((LiteralByteProtocol.protocol decoder).transcript H
      annotated.2.1.1 annotated.2.1.2 33).rounds)
    (checks : LiteralAcceptanceTerminal.Checks annotated.2.1.1 rs)
    (pubBytes : List SemanticPublicWire.Byte)
    (pub : R0P.Public SemanticPublicWire.M31)
    (hparse : SemanticPublicWire.parsePublic pubBytes = some pub)
    (hpublic : original.2.1.1 = SelectedTranscriptParams.publicStatement pubBytes pub hparse) :
    (∀ i < 33, LiteralTranscript.valid i (original.2.1.2 i)) ∧
      original.2.1.1.tag = 2 ∧ RawAdaptiveDecoderInjection.CommitmentMessages original.2.1.2 := by
  apply RawChecksInjectionFormat.checks_imply_injection_format
    decoder d P H original annotated horiginal hannotated rs hrows checks
  rw [hpublic]
  exact SelectedTranscriptParams.publicStatement_tag pubBytes pub hparse

/-- Counterexample to inferring htag from the public carrier alone. -/
theorem arbitrary_public_tag_counterexample (pub : LiteralTranscript.Public) :
    ({ pub with tag := 1 } : LiteralTranscript.Public).tag ≠ 2 := by
  change (1 : AspisV8R19.DuplexFrames.Byte) ≠ 2
  decide

#print axioms mapped_public_tag
#print axioms mapped_checks_format
#print axioms arbitrary_public_tag_counterexample
end AspisR1.RawDeployedTranscriptFormat
end
