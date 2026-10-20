import LiteralCheckedByteSpendExtractor
import RawCutTranscriptRun
import RawCutWordsFromRunExecutableBin
import RawEnrichedOpeningWordIdentity

/-! The actual enriched literal transcript's terminal checks, no-hit premise,
and successful fixed word bank suffice to produce the executable spend witness.
The opening word correspondence is derived from the enriched read and the
recorded-run transcript equation. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.RawRecordedChecksSpendExtractorBin

open AspisR1.LiteralTranscript
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.RawCutTranscriptRun
open AspisR1.RawCutWordsFromRunExecutableBin
open AspisR1.LiteralAcceptanceTerminal
open AspisR1.GSByteJointSpendExtractor
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- A terminal checks record on the actual 33-row enriched transcript, with a
clean classifier log and a nonfailing actual bank, yields the run's spend
witness. No successful read of the unenriched transcript, separately supplied
word-match, frame-compatibility, or support premises are needed. -/
theorem extractFromRun_of_checks_noHit_bank
    (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : Bytes → AspisR1.LiteralByteProtocol.State)
    (run : RawCutProverCompiler.RunView)
    (checks : LiteralAcceptanceTerminal.Checks run.2.1.1
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
        (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad run.2.1.1 []
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
        (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds)
    (coins : Coins)
    (hbank : ¬ AspisR1.GSConcreteByteDecoderBank.failed
      (AspisWide.GSConcreteReceivedWordInputs.fromWords (initialWordsFromRun run)
        (fun _ => finalWordFromRun run)) coins) :
    ∃ witness,
      RawCutWordsFromRunExecutableBin.extractFromRun checks.decoded run coins = some witness ∧
      AspisR1.SpendRelation.Rspend checks.decoded witness := by
  let pub := run.2.1.1
  let pf := run.2.1.2
  let rs := ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds
  have htrans := RawCutTranscriptRun.transcript_eq decoder (wordsFromRun run) H pub pf 33
  have hrounds :
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub
        (RawCutTranscriptRun.proof (wordsFromRun run) pf) 33).rounds =
        enrichRounds (wordsFromRun run) rs := by
    have hp := congrArg (fun P : LiteralTranscript.Prefix => P.rounds) htrans
    simpa [CanonicalCutEnrichedTranscript.enrichPrefix, rs, pub, pf] using hp
  have hread : LiteralOpeningView.read (enrichRounds (wordsFromRun run) rs) =
      some checks.view := by
    simpa [pub, pf, rs, hrounds] using checks.openingRead
  have hwordRun : checks.view.word = initialWordsFromRun run := by
    have hf := RawEnrichedOpeningWordIdentity.enriched_read_word_eq_fields
      (wordsFromRun run) rs checks.view hread
    simpa [initialWordsFromRun, LiteralOpeningView.eK] using hf.2.2
  have hwordFields := RawEnrichedOpeningWordIdentity.enriched_read_word_eq_fields
    (wordsFromRun run) rs checks.view hread
  have hW : initialWordsFromRun run =
      LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
        checks.view.c1 checks.view.c2 := by
    calc
      initialWordsFromRun run = checks.view.word := hwordRun.symm
      _ = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
          (wordsFromRun run).c1 (wordsFromRun run).c2 := hwordFields.2.2
      _ = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
          checks.view.c1 checks.view.c2 := by
            rw [← hwordFields.1, ← hwordFields.2.1]
  have hresult := LiteralCheckedByteSpendExtractor.extract_of_checks_noHit_bank
    decoder H pub (RawCutTranscriptRun.proof (wordsFromRun run) pf)
    checks hno (initialWordsFromRun run) hW (fun _ => finalWordFromRun run)
    coins hbank
  change ∃ witness,
    GSByteJointSpendExtractor.extract checks.decoded (initialWordsFromRun run)
      (fun _ => finalWordFromRun run) coins = some witness ∧
    AspisR1.SpendRelation.Rspend checks.decoded witness
  exact hresult

#print axioms extractFromRun_of_checks_noHit_bank

end AspisR1.RawRecordedChecksSpendExtractorBin
end
