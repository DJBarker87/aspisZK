import R1LiteralTerminalRunSpend
import R1GenericNoHitFS2

/-! A conditional interface for the terminal D3 implication. It collects the
existing model-reader and equation hypotheses; it does not prove that an
accepted verifier execution supplies them. The protocol still uses its
specification-level choice extractor; no efficient extraction claim is made. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralAcceptanceTerminal

open FS FS2
open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

attribute [local irreducible] LiteralClassifier.bad MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet
  MatchingSupport.match0 QueryResidualBridge.residuals sumcheckChecksZ

abbrev E := AspisWideTower.WideExact
abbrev TranscriptRounds :=
  List (LiteralTranscript.Message × LiteralTranscript.Challenge)

/-- All explicit model inputs needed by the existing conditional terminal
theorem. There is deliberately no Good/AcceptedPairing/cardinality field and
no extracted witness field. The supporting properties and witness are derived
by the terminal theorem from these checks and a separate no-hit hypothesis. -/
structure Checks (pub : LiteralTranscript.Public) (rs : TranscriptRounds) where
  decoded : R0P.Public SemanticPublicWire.M31
  view : LiteralOpeningView.View
  data : MatchingSupport.Data E
  publicParsed : SemanticPublicWire.parsePublic pub.pubBytes = some decoded
  matchingRead : LiteralMatchingData.read rs = some data
  openingRead : LiteralOpeningView.read rs = some view
  pairingChecks : LiteralPairingChecks.checks rs
  m31 : LiteralTranscript.Message
  queryBytes : List Nat
  state31 : State
  m32 : LiteralTranscript.Message
  rho : E
  state32 : State
  entry31 : rs[31]? = some (m31,
    (TranscriptView.Value.queries (.ok queryBytes), state31))
  entry32 : rs[32]? = some (m32,
    (TranscriptView.Value.ordinary rho, state32))
  valid31 : LiteralTranscript.valid 31 m31
  valid32 : LiteralTranscript.valid 32 m32
  queries : Fin 22 → Fin 262144
  queryDecode : LiteralQueryRead.decode queryBytes = some queries
  firstMatch : ∀ j, MatchingSupport.match0 data (queries j)
  residualBatch : ∑ j : Fin 22,
    (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
      QueryResidualBridge.residuals data queries j = 0
  claim : E
  polynomials : Fin 10 → Polynomial E
  claimParse : claimOf (SelectedSemanticPrefixFacts.lift view.semantic) = some claim
  polynomialParse : semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) =
    some polynomials
  semanticChecks : sumcheckChecksZ (maskClaimsR0 ConcretePackBasis.basis)
    (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
    ConcretePackBasis.basis
    (fun j => (view.semantic.map Prod.snd).getD j.val 0)
    ((view.semantic.map Prod.snd).getD 14 0) claim
    (fun j => (view.semantic.map Prod.snd).getD (15 + j.val) 0) polynomials
    (fun j l => data.Y ⟨j.val, by omega⟩ l) (data.Y 3)

/-- Parsed-and-checked spend witnesses inhabit the literal protocol relation. -/
theorem checked_implies_relation
    (pub : LiteralTranscript.Public)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (w : SpendRelation.Wspend)
    (hpub : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hcheck : SpendRelation.checkM31 decoded w = true) :
    LiteralProtocol.relation pub w := by
  refine ⟨decoded, hpub, ?_⟩
  exact (SpendRelation.check_eq_true_iff decoded w).mp hcheck

/-- On an actual 33-round byte-protocol transcript, the terminal model
conditions plus no classifier hit imply a witness for the protocol relation.
This is a conditional composition, not an acceptance-to-conditions theorem. -/
theorem checks_noHit_relation
    (decoder : LiteralByteProtocol.Decoder)
    (H : LiteralByteProtocol.Address → LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof)
    (checks : Checks pub
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds) :
    ∃ w, LiteralProtocol.relation pub w := by
  have hchecked := LiteralTerminalRunSpend.checked_witness_of_transcript_read_noHit
    decoder H pub pf 33 (by omega) checks.decoded checks.view checks.data
    checks.publicParsed checks.matchingRead checks.openingRead hno checks.pairingChecks
    checks.m31 checks.queryBytes checks.state31 checks.m32 checks.rho checks.state32
    checks.entry31 checks.entry32 checks.valid31 checks.valid32 checks.queries
    checks.queryDecode checks.firstMatch checks.residualBatch checks.claim
    checks.polynomials checks.claimParse checks.polynomialParse checks.semanticChecks
  obtain ⟨w, hw⟩ := hchecked
  exact ⟨w, checked_implies_relation pub checks.decoded w checks.publicParsed hw⟩

/-- The exact terminal premise consumed by generic FS2 D3. The model
conditions are supplied on accepted executions, and no-hit is supplied by D3's
terminal implication itself. -/
theorem conditional_d3
    (decoder : LiteralByteProtocol.Decoder)
    (V : LiteralTranscript.Public → LiteralByteProtocol.Proof →
      Program LiteralByteProtocol.Address LiteralByteProtocol.State Bool)
    (hconditions : ∀ (H : LiteralByteProtocol.Address → LiteralByteProtocol.State)
      (pub : LiteralTranscript.Public) (pf : LiteralByteProtocol.Proof),
      (eval H (V pub pf)).2 = true →
      Nonempty (Checks pub
        ((LiteralByteProtocol.protocol decoder).transcript H pub pf 33).rounds)) :
    FS2.D3 (LiteralByteProtocol.protocol decoder) LiteralByteProtocol.rows V := by
  apply GenericNoHitFS2.d3 (LiteralByteProtocol.protocol decoder)
    LiteralClassifier.bad LiteralProtocol.relation LiteralClassifier.budget V
  intro H pub pf haccepted hno
  obtain ⟨checks⟩ := hconditions H pub pf haccepted
  exact checks_noHit_relation decoder H pub pf checks hno

#print axioms checked_implies_relation
#print axioms checks_noHit_relation
#print axioms conditional_d3

end AspisR1.LiteralAcceptanceTerminal
end
