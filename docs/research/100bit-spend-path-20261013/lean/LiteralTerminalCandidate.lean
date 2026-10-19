import R1LiteralOpeningPrefixFacts
import R1LiteralSemanticParserFacts
import R1LiteralSemanticExcludedLift
import R1GenericNoHitIndex
import R1LiteralMatchingSemanticData
import R1LiteralTypedWords
import R1LiteralTypedContext
import R1LiteralSpendExtraction
import R1SemanticPrefix
import R1LiteralSemanticTerminalBridge
import R1PublicBaseMap
import R1SpendDataMap
import R1SemanticPublicWire

/-! Reuse the checked literal terminal proof up to its concrete candidate and
semantic production/copy-link facts. These facts can feed the executable
candidate-list witness scan. Accepted model checks and no-hit remain inputs;
this proves no source acceptance or probability claim. -/

set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralTerminalCandidate

open R0P R0P.Mask R0P.SemSource R0P.SemRounds R0C.SemStatement
open AspisR1.LiteralTranscript
open AspisV8R15.ExactTowerBase
open AspisWideTower AspisCircleGroupOrder SpendRelation
open AspisPool.AlgorithmicCircleDecoderV7

attribute [local irreducible] AspisR0.ListsResponses.Lambda LambdaRows
  AspisR1.InitialResponses.Lambda ConcreteBinding.candidates
  LiteralClassifier.bad semanticBadZ MatchingSupport.Good
  MatchingSupport.AcceptedPairing MatchingSupport.matchingSet sumcheckChecksZ
  SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase
  SelectedOpeningFunctionals.rows RawOpening.withRows

abbrev E := WideExact
abbrev embed := ExactBaseProjection.embed
abbrev eK := LiteralSemanticView.eK

theorem candidate_of_read_noHit
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
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3)) :
    ∃ t ∈ ConcreteBinding.candidates (LiteralTypedWords.word embed eK v.c1 v.c2),
      ProductionHolds (SpendDataMap.mapPublic embed decoded)
        ((v.semantic.map Prod.snd).getD 0 0)
        ((v.semantic.map Prod.snd).getD 1 0)
        (SemSource.rowsOf rowEquiv t) ∧
      CopyLinkBalance (SpendDataMap.mapPublic embed decoded)
        (SemSource.rowsOf rowEquiv t) := by
  let rs25 := rs.take 25

  -- Prefix readers, the recovered C2 identity and semantic payload parsing.
  have hprefix := LiteralOpeningPrefixFacts.read_prefix_components
    rs v hview
  rcases hprefix with ⟨hlen25, hc1, hc2, hsem, hword⟩
  have hno25 : ¬ GenericNoHit.hitFrom LiteralClassifier.bad pub [] rs25 :=
    GenericNoHitIndex.noHit_take LiteralClassifier.bad pub rs 25 hno
  have hexcluded := LiteralSemanticExcludedLift.excluded_lift
    pub decoded v.c1 rs25 v.semantic hpub hc1 hsem hno25
  obtain ⟨payloads, challenges, _hrounds, _hsemChals, hc2Z,
      _hclaimRows, _hpolysRows, _hdegree⟩ :=
    LiteralSemanticParserFacts.read_projection_facts eK rs25 v.semantic v.c2
      hsem hlen25 hc2

  -- The fixed literal semantic context and its C2 callback reproduce W.
  let x := LiteralTypedContext.context embed eK
    (SpendDataMap.mapPublic embed decoded)
    (PublicBaseMap.mapPublic_base embed decoded) v.c1 (fun _ => 0)
  let S := LiteralTypedWords.laneSubfield embed eK
  let F := embed.fieldRange
  let B := ConcretePackBasis.basis
  let cs := v.semantic.map Prod.snd
  let hw : InitialWord E := (LiteralSemanticPrefix.c2Pair eK v.c2).1
  let gw : InitialWord E := (LiteralSemanticPrefix.c2Pair eK v.c2).2
  have htransport : x.transport = AspisR1.rowEquiv := rfl
  have hpubTyped : PublicBase F x.pub := x.pubBase
  obtain ⟨common, hcommon, hW, hF, hF0⟩ :=
    LiteralMatchingSemanticData.read_matches_view rs d hmatching
  have hcommonEq : common = v := Option.some.inj (hcommon.symm.trans hview)
  subst common
  have hWliteral : d.W = LiteralTypedWords.word embed eK v.c1 v.c2 :=
    hW.trans hword
  have htyped : CandidateDescent.WordTyped S d.W := by
    rw [hWliteral]
    exact LiteralTypedWords.word_typed embed eK v.c1 v.c2
  have hpair : R0P.SemSource.c2Words x hw gw =
      LiteralTypedWords.word embed eK v.c1 v.c2 :=
    LiteralSemanticPayloadBridge.pair_c2Words
      embed eK (SpendDataMap.mapPublic embed decoded)
      (PublicBaseMap.mapPublic_base embed decoded) v.c1 v.c2 (fun _ => 0)
  have hwords : d.W = R0P.SemSource.c2Words x hw gw :=
    hWliteral.trans hpair.symm
  have hlanesF : ∀ l : Fin 29, l.val < 26 → S l = F := by
    intro l hl
    simp [S, F, LiteralTypedWords.laneSubfield,
      TypedRecoveredWords.laneSubfield, hl]

  -- The reader supplies the selected functionals. The generic bridge
  -- transports the matching predicates before specializing the field.
  obtain ⟨hviewF, hviewF0⟩ :=
    LiteralOpeningFunctionalFacts.read_functionals rs v hview

  -- Apply the old semantic terminal theorem with precisely its hypotheses.
  have hchecks' : sumcheckChecksZ (maskClaimsR0 B) x.pub B
      (fun j => cs.getD j.val 0) (cs.getD 14 0) claim
      (fun j => cs.getD (15 + j.val) 0) polys
      (fun j l => d.Y ⟨j.val, by omega⟩ l) (d.Y 3) := checks
  letI : CharP E AspisCircleGroupOrder.P :=
    charP_of_injective_algebraMap (algebraMap M31Exact E).injective AspisCircleGroupOrder.P
  -- Use the concrete carrier here: a local abbreviation makes the Point
  -- subtype conversion normalize the concrete tower unnecessarily.
  have terminal0 := LiteralSemanticTerminalBridge.large_matching_extracts_of_literal_prefix
    (E := AspisWideTower.WideExact) AspisCircleGroupOrder.P (by norm_num [AspisCircleGroupOrder.P])
    S F hlanesF B x htransport hpubTyped d htyped
  have terminalPoint := terminal0 (v.circlePoints 0)
  have terminalRounds := terminalPoint (SelectedSemanticPrefixFacts.lift v.semantic)
  have terminalChallenges := terminalRounds
    (by simpa [SelectedSemanticPrefixFacts.lift] using v.semantic_length)
    cs (by simpa [cs] using SelectedSemanticPrefixFacts.semChalsZ_lift v.semantic)
  have terminal1 := terminalChallenges claim hclaim polys hpolys
  have terminal2 := terminal1 hw gw
    (by simpa [hw, gw] using hc2Z) hwords
  have terminal3 := terminal2 (by
    intro i sm hmsg
    exact hexcluded i sm hmsg)
  have hresult := terminal3 v.circlePoints (hF.trans hviewF) (hF0.trans hviewF0)
    hgood haccepted hcard hchecks'
  rcases hresult with ⟨t, ht, ⟨hproduction, hcopy⟩, _⟩

  -- Expose the same terminal candidate and production facts to the actual
  -- list scanner instead of discarding them in an existential witness theorem.
  have hcandidate : t ∈ ConcreteBinding.candidates
      (LiteralTypedWords.word embed eK v.c1 v.c2) := by
    rw [hWliteral] at ht
    exact ht
  exact ⟨t, hcandidate, hproduction, hcopy⟩

#print axioms candidate_of_read_noHit

end AspisR1.LiteralTerminalCandidate
end
