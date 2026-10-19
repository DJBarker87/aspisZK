import GSByteJointSpendExtractorCompleteness

set_option autoImplicit false
namespace AspisR1.LiteralAcceptedExtractorEventCover

open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSConcreteReceivedWordInputs
open AspisR1.GSByteJointSpendExtractor
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1.GSByteJointSpendExtractorCompleteness

/-- The concrete accepted-execution premises needed by the GS extractor's
no-hit completeness theorem force a classifier hit or a real byte-bank abort
whenever extraction returns `none`. This is the deterministic event-cover
step; it does not assume either event is small. -/
theorem accepted_extraction_failure_covered
    (pub : LiteralTranscript.Public)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (d : MatchingSupport.Data E)
    (hpub : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hmatching : LiteralMatchingData.read rs = some d)
    (hview : LiteralOpeningView.read rs = some v)
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
    (hW : W = LiteralTypedWords.word embed eK v.c1 v.c2)
    (V : Fin 5 → FinalWord E) (coins : Coins)
    (hnone : extract decoded W V coins = none) :
    GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs ∨
      GSConcreteByteDecoderBank.failed (fromWords W V) coins := by
  by_cases hhit : GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs
  · exact Or.inl hhit
  by_cases hbank : GSConcreteByteDecoderBank.failed (fromWords W V) coins
  · exact Or.inr hbank
  have hno : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs := hhit
  obtain ⟨w, hw, _⟩ := extract_of_read_noHit pub decoded rs v d hpub hmatching hview hno
    hgood haccepted hcard claim polys hclaim hpolys checks W hW V coins hbank
  rw [hnone] at hw
  cases hw

#print axioms accepted_extraction_failure_covered
end AspisR1.LiteralAcceptedExtractorEventCover
