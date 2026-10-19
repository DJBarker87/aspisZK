import LiteralTerminalListExtract
import R1LiteralOpeningRunGood
import R1LiteralQueryRhoTranscriptSupport
import R1LiteralPairingChecks

/-! A transcript-indexed wrapper for the conditional literal terminal theorem.
The actual candidate-list scan returns a checked relation witness. Good, accepted pairing and matching-set cardinality are derived from the
no-hit transcript and the explicit coefficient/query check equations. This does not claim source refinement,
accepted-reader coverage, or probability closure. -/

set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralTerminalRunListExtract

open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV8R19.DuplexFrames

attribute [local irreducible] LiteralClassifier.bad MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet
  MatchingSupport.match0 QueryResidualBridge.residuals sumcheckChecksZ

theorem extract_of_transcript_read_noHit
    (decoder : LiteralByteProtocol.Decoder)
    (H : Bytes → LiteralByteProtocol.State)
    (pub : LiteralTranscript.Public)
    (pf : LiteralProtocol.Proof)
    (n : Nat) (hn : 33 ≤ n)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (v : LiteralOpeningView.View)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (hpub : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hmatching : LiteralMatchingData.read
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds = some d)
    (hview : LiteralOpeningView.read
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds = some v)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub []
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds)
    (hpairing : LiteralPairingChecks.checks
      ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds)
    (m31 : LiteralTranscript.Message) (xs : List Nat)
    (s31 : LiteralByteProtocol.State) (m32 : LiteralTranscript.Message)
    (rho : AspisWideTower.WideExact) (s32 : LiteralByteProtocol.State)
    (h31 : ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds[31]? =
      some (m31, (TranscriptView.Value.queries (.ok xs), s31)))
    (h32 : ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds[32]? =
      some (m32, (TranscriptView.Value.ordinary rho, s32)))
    (hvalid31 : LiteralTranscript.valid 31 m31)
    (hvalid32 : LiteralTranscript.valid 32 m32)
    (q : Fin 22 → Fin 262144)
    (hdecode : LiteralQueryRead.decode xs = some q)
    (hfirst : ∀ j, MatchingSupport.match0 d (q j))
    (hbatch : ∑ j : Fin 22,
      (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
        QueryResidualBridge.residuals d q j = 0)
    (claim : AspisWideTower.WideExact)
    (polys : Fin 10 → Polynomial AspisWideTower.WideExact)
    (hclaim : claimOf
      (SelectedSemanticPrefixFacts.lift v.semantic) = some claim)
    (hpolys : semPolysZ
      (SelectedSemanticPrefixFacts.lift v.semantic) = some polys)
    (checks : sumcheckChecksZ (maskClaimsR0 ConcretePackBasis.basis)
      (SpendDataMap.mapPublic ExactBaseProjection.embed decoded)
      ConcretePackBasis.basis
      (fun j => (v.semantic.map Prod.snd).getD j.val 0)
      ((v.semantic.map Prod.snd).getD 14 0) claim
      (fun j => (v.semantic.map Prod.snd).getD (15 + j.val) 0) polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (candidates : List CandidateListWitnessExtract.Tuple)
    (hlist : candidates.toFinset = ConcreteBinding.candidates
      (LiteralTypedWords.word ExactBaseProjection.embed LiteralSemanticView.eK
        v.c1 v.c2)) :
    ∃ w : Wspend, CandidateListWitnessExtract.extract decoded candidates = some w ∧
      Rspend decoded w := by
  let rs := ((LiteralByteProtocol.protocol decoder).transcript H pub pf n).rounds
  have hgood : MatchingSupport.Good d :=
    LiteralOpeningRunGood.good_of_transcript_read_noHit
      decoder H pub pf n (by omega) d hmatching hno
  have haccepted : MatchingSupport.AcceptedPairing d :=
    (LiteralPairingChecks.acceptedPairing_iff_checks rs d hmatching).mpr hpairing
  have hlen : 33 ≤ rs.length := by
    have hround : rs.length = n :=
      LiteralByteRunFacts.transcript_round decoder H pub pf n
    omega
  have hcard := LiteralQueryRhoTranscriptSupport.large_support_of_read_noHit
    pub rs hlen d hmatching hno m31 xs s31 m32 rho s32 h31 h32
    hvalid31 hvalid32 q hdecode hfirst hbatch
  exact LiteralTerminalListExtract.extract_of_read_noHit
    pub decoded rs v d hpub hmatching hview hno hgood haccepted hcard
    claim polys hclaim hpolys checks candidates hlist

#print axioms extract_of_transcript_read_noHit

end AspisR1.LiteralTerminalRunListExtract
end
