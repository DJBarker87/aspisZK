import LiteralFreshTerminalFailurePathDomination
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
end AspisR1.LiteralCheckedFailureMassBound
