import R1LiteralAcceptanceTerminal
import R1LiteralOpeningPrefixFacts
import R1LiteralSemanticParserFacts

/-! R16 reader-only composition. None of the reader hypotheses below is
claimed to follow from a deployed transaction. In particular semantic parsing
is not semantic acceptance. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.HchecksReaderComposition

open LiteralAcceptanceTerminal
open R0P.Mask R0C.SemStatement
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] MatchingSupport.match0 QueryResidualBridge.residuals
  QueryResidualBridge.values QueryResidualBridge.basis sumcheckChecksZ

/-- A matching read supplies its common view and both semantic parsers on
exactly the same list, without extra claim/polynomial hypotheses. -/
theorem matching_read_parsers (rs : TranscriptRounds)
    (data : MatchingSupport.Data E)
    (hmatching : LiteralMatchingData.read rs = some data) :
    ∃ (view : LiteralOpeningView.View) (claim : E)
      (polynomials : Fin 10 → Polynomial E),
      LiteralOpeningView.read rs = some view ∧
      claimOf (SelectedSemanticPrefixFacts.lift view.semantic) = some claim ∧
      semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) = some polynomials := by
  obtain ⟨view, _, _, _, _, _, _, _, hopen, _⟩ :=
    LiteralMatchingFacts.read_success_components rs data hmatching
  obtain ⟨hlen, _, hc2, hsem, _⟩ :=
    LiteralOpeningPrefixFacts.read_prefix_components rs view hopen
  obtain ⟨payloads, challenges, _, _, _, hclaim, hpolys, _⟩ :=
    LiteralSemanticParserFacts.read_projection_facts
      LiteralOpeningView.eK (rs.take 25) view.semantic view.c2 hsem hlen hc2
  exact ⟨view, SemanticPayloadView.claimAt14 payloads,
    (fun j => SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt payloads j)),
    hopen, hclaim, hpolys⟩

/-- The remaining R2 endpoint obligation, quantified only over successful
readers/parsers; the endpoint is the matching reader's Y, not an arbitrary
source accumulator. -/
def SemanticEndpoint (pub : R0P.Public SemanticPublicWire.M31)
    (rs : TranscriptRounds) (data : MatchingSupport.Data E) : Prop :=
  ∀ (view : LiteralOpeningView.View) (claim : E)
    (polynomials : Fin 10 → Polynomial E),
    LiteralOpeningView.read rs = some view →
    claimOf (SelectedSemanticPrefixFacts.lift view.semantic) = some claim →
    semPolysZ (SelectedSemanticPrefixFacts.lift view.semantic) = some polynomials →
    sumcheckChecksZ (maskClaimsR0 ConcretePackBasis.basis)
      (SpendDataMap.mapPublic ExactBaseProjection.embed pub) ConcretePackBasis.basis
      (fun j => (view.semantic.map Prod.snd).getD j.val 0)
      ((view.semantic.map Prod.snd).getD 14 0) claim
      (fun j => (view.semantic.map Prod.snd).getD (15 + j.val) 0) polynomials
      (fun j l => data.Y ⟨j.val, by omega⟩ l) (data.Y 3)

/-- Partial R16: all unproved acceptance/refinement inputs are explicit.
The common view, claim, polynomial family, their reads, and query decoder
are constructed rather than separately assumed. -/
theorem hchecks_partial
    (pub : LiteralTranscript.Public) (rs : TranscriptRounds)
    (decoded : R0P.Public SemanticPublicWire.M31)
    (data : MatchingSupport.Data E)
    (hpublic : SemanticPublicWire.parsePublic pub.pubBytes = some decoded)
    (hmatching : LiteralMatchingData.read rs = some data)
    (hpairing : LiteralPairingChecks.checks rs)
    (m31 : LiteralTranscript.Message) (queryBytes : List Nat) (state31 : State)
    (m32 : LiteralTranscript.Message) (rho : E) (state32 : State)
    (h31 : rs[31]? = some (m31,
      (TranscriptView.Value.queries (.ok queryBytes), state31)))
    (h32 : rs[32]? = some (m32,
      (TranscriptView.Value.ordinary rho, state32)))
    (hv31 : LiteralTranscript.valid 31 m31)
    (hv32 : LiteralTranscript.valid 32 m32)
    (hq : queryBytes.Nodup ∧ queryBytes.length = 22 ∧
      ∀ x ∈ queryBytes, x < 262144)
    (hfirst : ∀ q : Fin 22 → Fin 262144,
      LiteralQueryRead.decode queryBytes = some q →
      ∀ j, MatchingSupport.match0 data (q j))
    (haccum : ∀ q : Fin 22 → Fin 262144,
      LiteralQueryRead.decode queryBytes = some q →
      (∑ l : Fin 64, data.f l * LiteralOpeningView.eK
        (∑ j : Fin 22, (SelectedChallengeMap.rhoOf rho) ^ j.val *
          QueryResidualBridge.basis q j l)) =
      ∑ j : Fin 22, (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
        QueryResidualBridge.values data q j)
    (hsemantic : SemanticEndpoint decoded rs data) :
    Nonempty (Checks pub rs) := by
  obtain ⟨view, claim, polynomials, hopen, hclaim, hpolys⟩ :=
    matching_read_parsers rs data hmatching
  let queries : Fin 22 → Fin 262144 :=
    (AspisV8R19.R412LegalQueryEnumeration.legalOfList
      queryBytes hq.1 hq.2.1 hq.2.2).val
  have hdecode : LiteralQueryRead.decode queryBytes = some queries := by
    simp only [LiteralQueryRead.decode, dif_pos hq, queries]
  have hbatch : ∑ j : Fin 22,
      (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
        QueryResidualBridge.residuals data queries j = 0 := by
    apply QueryResidualBridge.accumulated_equation_implies_residual_batch
      (K := AspisV8R15.ExactTowerBase.QM31Exact) (E := E)
      LiteralOpeningView.eK data queries (SelectedChallengeMap.rhoOf rho)
    exact haccum queries hdecode
  exact ⟨{
    decoded := decoded, view := view, data := data
    publicParsed := hpublic, matchingRead := hmatching, openingRead := hopen
    pairingChecks := hpairing
    m31 := m31, queryBytes := queryBytes, state31 := state31
    m32 := m32, rho := rho, state32 := state32
    entry31 := h31, entry32 := h32, valid31 := hv31, valid32 := hv32
    queries := queries, queryDecode := hdecode
    firstMatch := hfirst queries hdecode, residualBatch := hbatch
    claim := claim, polynomials := polynomials
    claimParse := hclaim, polynomialParse := hpolys
    semanticChecks := hsemantic view claim polynomials hopen hclaim hpolys }⟩

#print axioms matching_read_parsers
#print axioms hchecks_partial
end AspisR1.HchecksReaderComposition
end
