import LiteralTerminalCandidate
import CandidateListWitnessExtract

set_option autoImplicit false

namespace AspisR1.LiteralTerminalListExtract

open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7

attribute [local irreducible] ConcreteBinding.candidates
  AspisR0.ListsResponses.Lambda AspisR1.InitialResponses.Lambda
  LiteralClassifier.bad semanticBadZ MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet sumcheckChecksZ

abbrev E := WideExact
abbrev embed := ExactBaseProjection.embed
abbrev eK := LiteralSemanticView.eK

/-- Literal parsed semantic checks outside the existing bad events force the
actual supplied candidate-list scan to return a checked spend witness.
The list correspondence remains the executable producer's explicit obligation. -/
theorem extract_of_read_noHit
    (pub : LiteralTranscript.Public)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (d : MatchingSupport.Data E)
    (hpub : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hmatching : LiteralMatchingData.read rs = some d)
    (hview : LiteralOpeningView.read rs = some v)
    (hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs)
    (hgood : MatchingSupport.Good d)
    (haccepted : MatchingSupport.AcceptedPairing d)
    (hcard : 9558 ≤ (MatchingSupport.matchingSet d).card)
    (claim : E) (polys : Fin 10 → Polynomial E)
    (hclaim : claimOf (SelectedSemanticPrefixFacts.lift v.semantic) = some claim)
    (hpolys : semPolysZ (SelectedSemanticPrefixFacts.lift v.semantic) = some polys)
    (checks : sumcheckChecksZ (maskClaimsR0 ConcretePackBasis.basis)
      (SpendDataMap.mapPublic embed decoded) ConcretePackBasis.basis
      (fun j => (v.semantic.map Prod.snd).getD j.val 0)
      ((v.semantic.map Prod.snd).getD 14 0) claim
      (fun j => (v.semantic.map Prod.snd).getD (15 + j.val) 0) polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3))
    (candidates : List CandidateListWitnessExtract.Tuple)
    (hlist : candidates.toFinset = ConcreteBinding.candidates
      (LiteralTypedWords.word embed eK v.c1 v.c2)) :
    ∃ w, CandidateListWitnessExtract.extract decoded candidates = some w ∧
      Rspend decoded w := by
  have hex := LiteralTerminalCandidate.candidate_of_read_noHit
    pub decoded rs v d hpub hmatching hview hno hgood haccepted hcard
    claim polys hclaim hpolys checks
  have hshape : PublicOptionShape.canonical decoded :=
    SemanticPublicWire.parsePublic_canonical pub.pubBytes decoded hpub
  let S := LiteralTypedWords.laneSubfield embed eK
  have hlanes : ∀ l : Fin 29, l.val < 26 → S l = embed.fieldRange := by
    intro l hl
    simp [S, LiteralTypedWords.laneSubfield, TypedRecoveredWords.laneSubfield, hl]
  have htyped : CandidateDescent.WordTyped S
      (LiteralTypedWords.word embed eK v.c1 v.c2) :=
    LiteralTypedWords.word_typed embed eK v.c1 v.c2
  exact CandidateListWitnessExtract.complete_of_typed_candidate_list
    decoded hshape S hlanes (LiteralTypedWords.word embed eK v.c1 v.c2)
    htyped candidates hlist ((v.semantic.map Prod.snd).getD 0 0)
    ((v.semantic.map Prod.snd).getD 1 0) hex

#print axioms extract_of_read_noHit

end AspisR1.LiteralTerminalListExtract
