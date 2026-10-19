import GSByteJointSpendExtractorCompleteness
import R1LiteralByteProtocol
import R1LiteralAcceptanceTerminal
import R1LiteralOpeningRunGood
import R1LiteralQueryRhoTranscriptSupport
import R1LiteralPairingChecks

/-! Actual byte-bank extraction from terminal checks plus a clean classifier
transcript.  The point-word correspondence remains an explicit premise, so
this theorem does not silently identify the model view with received bytes. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralCheckedByteSpendExtractor

open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open AspisR1.LiteralAcceptanceTerminal
open AspisR1.GSByteJointSpendExtractor
open AspisWide.GSConcreteReceivedWordInputs
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

attribute [local irreducible] LiteralClassifier.bad MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet
  MatchingSupport.match0 QueryResidualBridge.residuals sumcheckChecksZ
  GSByteJointSpendExtractor.extract

abbrev E := AspisWideTower.WideExact
abbrev embed := ExactBaseProjection.embed
abbrev eK := LiteralSemanticView.eK

/-- On the actual 33-row transcript, terminal checks and no classifier hit
derive all matching-support premises consumed by the byte-bank extractor.
The exact typed received-word equality is left explicit. -/
theorem extract_of_checks_noHit_bank
    (decoder : AspisR1.LiteralByteProtocol.Decoder)
    (H : AspisV8R19.DuplexFrames.Bytes → AspisR1.LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public) (pf : Nat → LiteralTranscript.Message)
    (checks : LiteralAcceptanceTerminal.Checks pub
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    (W : Fin 29 → InitialWord E)
    (hW : W = LiteralTypedWords.word embed eK checks.view.c1 checks.view.c2)
    (V : Fin 5 → FinalWord E)
    (coins : GSByteJointSpendExtractor.Coins)
    (hbank : ¬ GSConcreteByteDecoderBank.failed (fromWords W V) coins) :
    ∃ w, GSByteJointSpendExtractor.extract checks.decoded W V coins = some w ∧
      Rspend checks.decoded w := by
  let rs := ((AspisR1.LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds
  have hgood : MatchingSupport.Good checks.data :=
    LiteralOpeningRunGood.good_of_transcript_read_noHit
      decoder H pub pf 33 (by omega) checks.data checks.matchingRead hno
  have haccepted : MatchingSupport.AcceptedPairing checks.data :=
    (LiteralPairingChecks.acceptedPairing_iff_checks rs checks.data
      checks.matchingRead).mpr checks.pairingChecks
  have hlen : 33 ≤ rs.length := by
    have hround : rs.length = 33 :=
      LiteralByteRunFacts.transcript_round decoder H pub pf 33
    omega
  have hcard := LiteralQueryRhoTranscriptSupport.large_support_of_read_noHit
    pub rs hlen checks.data checks.matchingRead hno
    checks.m31 checks.queryBytes checks.state31 checks.m32 checks.rho checks.state32
    checks.entry31 checks.entry32 checks.valid31 checks.valid32 checks.queries
    checks.queryDecode checks.firstMatch checks.residualBatch
  exact GSByteJointSpendExtractorCompleteness.extract_of_read_noHit
    pub checks.decoded rs checks.view checks.data checks.publicParsed
    checks.matchingRead checks.openingRead hno hgood haccepted hcard
    checks.claim checks.polynomials checks.claimParse checks.polynomialParse
    checks.semanticChecks W hW V coins hbank

#print axioms extract_of_checks_noHit_bank

end AspisR1.LiteralCheckedByteSpendExtractor
end
