import GSByteJointSpendExtractor

set_option autoImplicit false
namespace AspisR1.GSByteJointSpendExtractorCompleteness

open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSConcreteReceivedWordInputs
open AspisR1.GSByteJointSpendExtractor
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

attribute [local irreducible] ConcreteBinding.candidates
  LiteralClassifier.bad semanticBadZ MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet sumcheckChecksZ
  GSByteJointSpendExtractor.extract

abbrev E := WideExact
abbrev embed := ExactBaseProjection.embed
abbrev eK := LiteralSemanticView.eK

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
    (hW : W = LiteralTypedWords.word embed eK v.c1 v.c2)
    (V : Fin 5 → FinalWord E) (coins : GSByteJointSpendExtractor.Coins)
    (hbank : ¬ GSConcreteByteDecoderBank.failed (fromWords W V) coins) :
    ∃ w, GSByteJointSpendExtractor.extract decoded W V coins = some w ∧
      Rspend decoded w := by
  cases hr : GSConcreteByteDecoderBank.run (fromWords W V) coins with
  | none =>
    apply False.elim
    apply hbank
    apply (GSRejectingSamplerDecoderBank.failed_iff_output
      (M31RetryOutputFiber.actualWidePairSamplerTape 21377328)
      (M31AcceptFiber.P31^8) (fromWords W V) coins).2
    exact Or.inl hr
  | some out =>
    have hcomplete := GSByteJointSpendExtractor.decodedLists_complete W V coins out hr hbank
    obtain ⟨w, hw, hvalid⟩ := LiteralComputedCandidateExtract.extract_of_read_noHit
      pub decoded rs v d hpub hmatching hview hno hgood haccepted hcard
      claim polys hclaim hpolys checks W (GSByteJointSpendExtractor.decodedLists W out)
      hW hcomplete
    refine ⟨w, ?_, hvalid⟩
    simpa only [GSByteJointSpendExtractor.extract, hr, Option.bind_some] using hw

theorem failure_mass_small
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
    (hW : W = LiteralTypedWords.word embed eK v.c1 v.c2)
    (V : Fin 5 → FinalWord E) :
    mean (fun coins : GSByteJointSpendExtractor.Coins =>
      indicator (GSByteJointSpendExtractor.extract decoded W V coins = none)) <
        (1/2 : ℚ)^126 := by
  have hpoint : ∀ coins : GSByteJointSpendExtractor.Coins,
      indicator (GSByteJointSpendExtractor.extract decoded W V coins = none) ≤
        indicator (GSConcreteByteDecoderBank.failed (fromWords W V) coins) := by
    intro coins
    apply FS.indicator_mono
    intro hnone
    by_contra hbank
    obtain ⟨w, hw, _⟩ := extract_of_read_noHit
      pub decoded rs v d hpub hmatching hview hno hgood haccepted hcard
      claim polys hclaim hpolys checks W hW V coins hbank
    rw [hnone] at hw
    cases hw
  exact (FS.mean_mono hpoint).trans_lt
    (GSConcreteByteDecoderBank.failure_small (fromWords W V))

#print axioms extract_of_read_noHit
#print axioms failure_mass_small
end AspisR1.GSByteJointSpendExtractorCompleteness
