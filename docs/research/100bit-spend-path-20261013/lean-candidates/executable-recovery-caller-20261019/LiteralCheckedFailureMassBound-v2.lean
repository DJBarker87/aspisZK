import LiteralFreshTerminalFailurePathDomination
import RawEnrichedOpeningWordIdentity
import LiteralCheckedByteSpendExtractor

set_option autoImplicit false
namespace AspisR1.LiteralCheckedFailureMassBound

open AspisR1.LiteralTranscript
open AspisR1.LiteralFreshTerminalFailurePathDomination
open AspisR1.LiteralFreshBankAbortComposition
open AspisR1.LiteralCheckedByteSpendExtractor
open AspisR1.GSByteJointSpendExtractor
open AspisR1.GSConcreteByteDecoderBank
open AspisWide.GSConcreteReceivedWordInputs
open AspisPool.AlgorithmicCircleDecoderV7

attribute [local irreducible] LiteralByteProtocol.protocol
  RawCutTranscriptRun.proof RawCutWordsFromRunExecutable.wordsFromRun
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisWideTower AspisV8R15.ExactTowerBase
open FS FS2

/-- For a fixed checked transcript, extractor failure under fresh bank coins
is pointwise contained in bank abort whenever the transcript has no classifier
hit. This turns the deterministic Checks-facing extraction theorem into the
terminal conditional-mass premise for the fresh-path averaging theorem. -/
theorem checked_extractor_none_mass_le_bank_abort
    (decoder : LiteralByteProtocol.Decoder)
    (H : AspisV8R19.DuplexFrames.Bytes → LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public) (pf : Nat → LiteralTranscript.Message)
    (checks : LiteralAcceptanceTerminal.Checks pub
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    (W : Fin 29 → InitialWord WideExact)
    (hW : W = LiteralTypedWords.word embed eK checks.view.c1 checks.view.c2)
    (V : Fin 5 → FinalWord WideExact) :
    mean (fun coins : Coins => indicator
      (extract checks.decoded W V coins = none)) ≤ bankAbortMass (fromWords W V) := by
  apply clean_failure_mass_le_abort_mass
    (failure := fun coins : Coins => extract checks.decoded W V coins = none)
    (abort := fun coins : Coins => failed (fromWords W V) coins)
    (hit := GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    ?_ hno
  intro coins hfail
  by_cases hbank : failed (fromWords W V) coins
  · exact Or.inr hbank
  · obtain ⟨w, hw, _hvalid⟩ :=
      extract_of_checks_noHit_bank decoder H pub pf checks hno W hW V coins hbank
    rw [hfail] at hw
    cases hw

#print axioms checked_extractor_none_mass_le_bank_abort

/-- The recorded-run version of the fixed-log failure-mass bound.  A successful
opening read of the metadata-enriched transcript identifies its C1/C2 typed
words with the raw-run words, so the explicit W-match needed by the Checks
adapter is derived rather than assumed. -/
theorem checked_run_extractor_none_mass_le_bank_abort
    (decoder : LiteralByteProtocol.Decoder)
    (H : AspisV8R19.DuplexFrames.Bytes → LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof)
    (run : RawCutProverCompiler.RunView)
    (checks : LiteralAcceptanceTerminal.Checks pub
      ((LiteralByteProtocol.protocol decoder).transcript H pub
        (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutable.wordsFromRun run) pf) 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((LiteralByteProtocol.protocol decoder).transcript H pub
        (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutable.wordsFromRun run) pf) 33).rounds) :
    mean (fun coins : RawCoins => indicator
      (extract checks.decoded (RawCutWordsFromRunExecutable.initialWordsFromRun run)
        (fun _ => RawCutWordsFromRunExecutable.finalWordFromRun run) coins = none)) ≤
      bankAbortMass (fromWords
        (RawCutWordsFromRunExecutable.initialWordsFromRun run)
        (fun _ => RawCutWordsFromRunExecutable.finalWordFromRun run)) := by
  let rawRs := ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds
  have htrans := RawCutTranscriptRun.transcript_eq decoder
    (RawCutWordsFromRunExecutable.wordsFromRun run) H pub pf 33
  have hrounds :
      (((LiteralByteProtocol.protocol decoder).transcript H pub
        (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutable.wordsFromRun run) pf) 33) : Prefix).rounds =
        CanonicalCutEnrichedTranscript.enrichRounds
          (RawCutWordsFromRunExecutable.wordsFromRun run) rawRs := by
    conv_lhs => rw [htrans]
    rfl
  have hread : LiteralOpeningView.read
      (CanonicalCutEnrichedTranscript.enrichRounds
        (RawCutWordsFromRunExecutable.wordsFromRun run) rawRs) = some checks.view := by
    rw [← hrounds]
    exact checks.openingRead
  have hfields := RawEnrichedOpeningWordIdentity.enriched_read_word_eq_fields
    (RawCutWordsFromRunExecutable.wordsFromRun run) rawRs checks.view hread
  have hW : RawCutWordsFromRunExecutable.initialWordsFromRun run =
      LiteralTypedWords.word ExactBaseProjection.embed LiteralSemanticView.eK
        checks.view.c1 checks.view.c2 := by
    change LiteralTypedWords.word ExactBaseProjection.embed LiteralSemanticView.eK
        (RawCutWordsFromRunExecutable.wordsFromRun run).c1
        (RawCutWordsFromRunExecutable.wordsFromRun run).c2 = _
    rw [hfields.1, hfields.2.1]
  exact checked_extractor_none_mass_le_bank_abort decoder H pub
    (RawCutTranscriptRun.proof (RawCutWordsFromRunExecutable.wordsFromRun run) pf)
    checks hno (RawCutWordsFromRunExecutable.initialWordsFromRun run) hW
    (fun _ => RawCutWordsFromRunExecutable.finalWordFromRun run)

#print axioms checked_run_extractor_none_mass_le_bank_abort
end AspisR1.LiteralCheckedFailureMassBound
