import RawChecksInjectionFormat
import RawAdaptiveDecoderInjection

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.RawChecksAdaptiveInjection

open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.RawCutProverCompiler
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutWordsFromView
open AspisR1.LiteralTranscript
open AspisR1.RawAdaptiveDecoderInjection

abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

/-- The compiler's actual adaptive injection can consume checked acceptance
directly.  The fixed public tag and the original first-read budget remain
explicit; row constructors and strict commitment payload parsing are derived
from Checks on the annotated run. -/
def injection_of_checked_acceptance
    (decoder : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hQ : ∀ H : Bytes → State, firstReads emptyTable
      (eval H (experiment P (verifier decoder d))).1 ≤ Q)
    (htag : ∀ H : Bytes → State,
      (eval H (experiment P (verifier decoder d))).2.1.1.tag = 2)
    (hchecks : ∀ H : Bytes → State,
      FS2.accepts (eval H (experiment P (verifier decoder d))) →
      LiteralAcceptanceTerminal.Checks
        (eval H (experiment
          (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
          (verifier decoder d))).2.1.1
        (((LiteralByteProtocol.protocol decoder).transcript H
          (eval H (experiment
            (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
            (verifier decoder d))).2.1.1
          (eval H (experiment
            (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
            (verifier decoder d))).2.1.2 33).rounds)) :
    AcceptedAdaptiveFiatShamir.LazyInj (LiteralByteProtocol.protocol decoder)
      (RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select
        LiteralTableWordChoice.choose)
      (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
      (verifier decoder d) kappa Q := by
  apply RawAdaptiveDecoderInjection.injection decoder d P Q hQ
  intro H hacc
  let original := eval H (experiment P (verifier decoder d))
  let annotated := eval H
    (experiment (compiled decoder d (RawCutWordsFromView.buildWords decoder) P)
      (verifier decoder d))
  have hfmt := RawChecksInjectionFormat.checks_imply_injection_format
    decoder d P H original annotated rfl rfl
    (((LiteralByteProtocol.protocol decoder).transcript H
    annotated.2.1.1 annotated.2.1.2 33).rounds) rfl (hchecks H hacc) (htag H)
  exact hfmt

#print axioms injection_of_checked_acceptance
end AspisR1.RawChecksAdaptiveInjection
end
