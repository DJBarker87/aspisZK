import LiteralTerminalListExtract
import GSConcreteInitialRuntimeJointCandidates

set_option autoImplicit false
namespace AspisR1.LiteralComputedCandidateExtract

open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSConcreteInitialRuntimeJointCandidates

attribute [local irreducible] ConcreteBinding.candidates
  AspisWide.GSConcreteInitialRuntimeJointCandidates.jointCandidates
  LiteralClassifier.bad semanticBadZ MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet sumcheckChecksZ

abbrev E := WideExact
abbrev embed := ExactBaseProjection.embed
abbrev eK := LiteralSemanticView.eK

/-- Actual runtime joint candidate construction followed by the checked scan.
No candidate set enumeration or global witness selection is used. -/
def extract (pub : Public M31Exact) (W : Fin 29 → InitialWord E)
    (decodedLists : Fin 29 → List (InitialMessage E)) : Option Wspend :=
  CandidateListWitnessExtract.extract pub (jointCandidates W decodedLists)

def scanCount (pub : Public M31Exact) (W : Fin 29 → InitialWord E)
    (decodedLists : Fin 29 → List (InitialMessage E)) : Nat :=
  CandidateListWitnessExtract.scanCount pub (jointCandidates W decodedLists)

theorem returned_valid (pub : Public M31Exact) (W : Fin 29 → InitialWord E)
    (decodedLists : Fin 29 → List (InitialMessage E)) (w : Wspend)
    (h : extract pub W decodedLists = some w) : Rspend pub w :=
  CandidateListWitnessExtract.returned_valid pub _ w h

theorem scanCount_le_100 (pub : Public M31Exact) (W : Fin 29 → InitialWord E)
    (decodedLists : Fin 29 → List (InitialMessage E)) :
    scanCount pub W decodedLists ≤ 100 :=
  CandidateListWitnessExtract.scanCount_le_100 pub _
    (jointCandidates_length_le_100 W decodedLists)

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
    (W : Fin 29 → InitialWord E)
    (decodedLists : Fin 29 → List (InitialMessage E))
    (hW : W = LiteralTypedWords.word embed eK v.c1 v.c2)
    (hcomplete : ∀ lane, InitialResponses.Close (W lane) ⊆
      (decodedLists lane).toFinset) :
    ∃ w, extract decoded W decodedLists = some w ∧ Rspend decoded w := by
  have hlist := jointCandidates_to_bindingCandidates W decodedLists hcomplete
  have hlist' : (jointCandidates W decodedLists).toFinset =
      ConcreteBinding.candidates (LiteralTypedWords.word embed eK v.c1 v.c2) :=
    hlist.trans (congrArg ConcreteBinding.candidates hW)
  change ∃ w, CandidateListWitnessExtract.extract decoded
    (jointCandidates W decodedLists) = some w ∧ Rspend decoded w
  exact LiteralTerminalListExtract.extract_of_read_noHit
    pub decoded rs v d hpub hmatching hview hno hgood haccepted hcard
    claim polys hclaim hpolys checks (jointCandidates W decodedLists) hlist'

#print axioms extract
#print axioms returned_valid
#print axioms scanCount_le_100
#print axioms extract_of_read_noHit

end AspisR1.LiteralComputedCandidateExtract
