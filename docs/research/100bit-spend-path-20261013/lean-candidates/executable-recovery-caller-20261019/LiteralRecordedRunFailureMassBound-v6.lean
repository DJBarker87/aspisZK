import LiteralCheckedFailureMassBound
import RawRecordedChecksSpendExtractor

set_option autoImplicit false
namespace AspisR1.LiteralRecordedRunFailureMassBound

open AspisR1.LiteralFreshTerminalFailurePathDomination
open AspisR1.LiteralFreshBankAbortComposition
open AspisR1.RawCutWordsFromRunExecutable
open AspisR1.RawRecordedChecksSpendExtractor
open AspisR1.GSConcreteByteDecoderBank
open AspisR1.GSByteJointSpendExtractor
open AspisR1.LiteralAcceptanceTerminal
open AspisWide.GSConcreteReceivedWordInputs
open AspisV8R19.DuplexFrames
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open FS FS2

/-- For an actual recorded run whose enriched transcript passes the terminal
checks and has no classifier hit, failure of the real run-level extractor is
contained in failure of the actual independently sampled GS byte bank. The
typed opening word is recovered inside `extractFromRun_of_checks_noHit_bank`;
this caller needs no separately supplied word-match premise. -/
theorem recorded_run_extractor_none_mass_le_bank_abort
    (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : Bytes → AspisR1.LiteralByteProtocol.State)
    (run : RawCutProverCompiler.RunView)
    (checks : Checks run.2.1.1
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
        (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom AspisR1.LiteralClassifier.bad run.2.1.1 []
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
        (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds) :
    mean (fun coins : RawCoins => indicator
      (extractFromRun checks.decoded run coins = none)) ≤
      bankAbortMass (fromWords (initialWordsFromRun run)
        (fun _ => finalWordFromRun run)) := by
  apply clean_failure_mass_le_abort_mass
    (failure := fun coins : RawCoins =>
      extractFromRun checks.decoded run coins = none)
    (abort := fun coins : RawCoins =>
      failed (fromWords (initialWordsFromRun run)
        (fun _ => finalWordFromRun run)) coins)
    (hit := GenericNoHit.hitFrom AspisR1.LiteralClassifier.bad run.2.1.1 []
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H run.2.1.1
        (RawCutTranscriptRun.proof (wordsFromRun run) run.2.1.2) 33).rounds)
    ?_ hno
  intro coins hfail
  by_cases hbank : failed (fromWords (initialWordsFromRun run)
    (fun _ => finalWordFromRun run)) coins
  · exact Or.inr hbank
  · obtain ⟨witness, hw, _hvalid⟩ :=
      extractFromRun_of_checks_noHit_bank decoder H run checks hno coins hbank
    rw [hfail] at hw
    cases hw

#print axioms recorded_run_extractor_none_mass_le_bank_abort

end AspisR1.LiteralRecordedRunFailureMassBound
