import OraclePortSemanticProjectionC6

/-! An observation-only arithmetic and semantic interface for the existing
clean-model consumer. Full words remain attached to its reader/extractor,
while the checks read only the local folds and transcript scalar projections. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortSelectedConsumerC6
open LiteralAcceptanceTerminal R0P.Mask R0C.SemStatement R0P.SemSource
open OraclePortSelectedObservationsC6
attribute [local irreducible] MatchingSupport.AcceptedPairing MatchingSupport.match0
  QueryResidualBridge.values QueryResidualBridge.basis HchecksAccumulator.ClosedSum
  sumcheckChecksZ terminalZ maskClaimsR0 SpendDataMap.mapPublic

def terminal (pub : R0P.Public SemanticPublicWire.M31)
    (d : MatchingSupport.Data E) (cs : List E) : E :=
  terminalZ (maskClaimsR0 ConcretePackBasis.basis)
    (SpendDataMap.mapPublic ExactBaseProjection.embed pub)
    (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 13 0) (cs.getD 14 0)
    (preZc (fun j => cs.getD j.val 0)) ConcretePackBasis.basis
    (fun j l => d.Y ⟨j.val,by omega⟩ l) (d.Y 3)
    (fun j => cs.getD (15+j.val) 0)

def Semantic (pub : R0P.Public SemanticPublicWire.M31)
    (o : OraclePortSelectedObservationsC6.Observation)
    (s : OraclePortSemanticProjectionC6.Observation) : Prop :=
  match s.claim,s.polynomials with
  | some claim,some polys => R3SemanticEquationCore.Equations claim
      (terminal pub o.scalars s.challenges)
      (fun j => s.challenges.getD (15+j.val) 0) polys
  | _,_ => False

theorem semantic_iff (pub : R0P.Public SemanticPublicWire.M31)
    (d : MatchingSupport.Data E) (q : Fin 22 → Fin 262144)
    (v : LiteralOpeningView.View) (claim : E) (polys : Fin 10 → Polynomial E)
    (hc : claimOf (SelectedSemanticPrefixFacts.lift v.semantic) = some claim)
    (hp : semPolysZ (SelectedSemanticPrefixFacts.lift v.semantic) = some polys) :
    Semantic pub (observe d q) (OraclePortSemanticProjectionC6.observe v.semantic) ↔
      R3SemanticEquationCore.Equations claim (R3SemanticRemainingJoins.terminal pub v d)
        (fun j => (v.semantic.map Prod.snd).getD (15+j.val) 0) polys := by
  simp only [Semantic,OraclePortSemanticProjectionC6.observe,hc,hp]
  rfl

/-- No whole-row or whole-word equality appears among the arithmetic checks. -/
structure Checks (pub : LiteralTranscript.Public) (rs : TranscriptRounds) where
  decoded : R0P.Public SemanticPublicWire.M31
  data : MatchingSupport.Data E
  view : LiteralOpeningView.View
  publicParsed : SemanticPublicWire.parsePublic pub.pubBytes = some decoded
  matchingRead : LiteralMatchingData.read rs = some data
  openingRead : LiteralOpeningView.read rs = some view
  m31 : LiteralTranscript.Message
  queryBytes : List Nat
  state31 : AspisV8R19.SourceDuplexStep.State
  m32 : LiteralTranscript.Message
  rho : E
  state32 : AspisV8R19.SourceDuplexStep.State
  entry31 : rs[31]? = some (m31,(TranscriptView.Value.queries (.ok queryBytes),state31))
  entry32 : rs[32]? = some (m32,(TranscriptView.Value.ordinary rho,state32))
  valid31 : LiteralTranscript.valid 31 m31
  valid32 : LiteralTranscript.valid 32 m32
  queries : Fin 22 → Fin 262144
  queryDecode : LiteralQueryRead.decode queryBytes = some queries
  writer : Writer (observe data queries)
  backend : Backend (observe data queries) queries (SelectedChallengeMap.rhoOf rho)
  semantic : Semantic decoded (observe data queries) (OraclePortSemanticProjectionC6.observe view.semantic)

/-- Selected observations suffice for the exact retained terminal consumer.
The reader's full words are retained; they are not replaced in the extractor. -/
theorem toLiteral_nonempty {pub : LiteralTranscript.Public} {rs : TranscriptRounds}
    (c : Checks pub rs) : Nonempty (LiteralAcceptanceTerminal.Checks pub rs) := by
  obtain ⟨v,claim,polys,hopen,hclaim,hpolys⟩ :=
    HchecksReaderComposition.matching_read_parsers rs c.data c.matchingRead
  have same : v = c.view := Option.some.inj (hopen.symm.trans c.openingRead)
  subst v
  obtain ⟨pairing,closed⟩ := (backend_iff _ _ _).1 c.backend
  have equations := (semantic_iff c.decoded c.data c.queries c.view claim polys hclaim hpolys).1 c.semantic
  exact ⟨{
    decoded := c.decoded,view := c.view,data := c.data
    publicParsed := c.publicParsed,matchingRead := c.matchingRead,openingRead := c.openingRead
    pairingChecks := (LiteralPairingChecks.acceptedPairing_iff_checks rs c.data c.matchingRead).1 pairing
    m31 := c.m31,queryBytes := c.queryBytes,state31 := c.state31
    m32 := c.m32,rho := c.rho,state32 := c.state32
    entry31 := c.entry31,entry32 := c.entry32,valid31 := c.valid31,valid32 := c.valid32
    queries := c.queries,queryDecode := c.queryDecode
    firstMatch := (writer_iff _ _).1 c.writer
    residualBatch := HchecksAccumulator.residual_of_closed_sum LiteralOpeningView.eK _ _ _ closed
    claim := claim,polynomials := polys,claimParse := hclaim,polynomialParse := hpolys
    semanticChecks := ⟨R3SemanticEquationCore.parsed_degrees rs c.view polys c.openingRead hpolys,equations⟩ }⟩

def toLiteral {pub : LiteralTranscript.Public} {rs : TranscriptRounds}
    (c : Checks pub rs) : LiteralAcceptanceTerminal.Checks pub rs :=
  Classical.choice (toLiteral_nonempty c)

/-- The old model check package implies the new observation interface. -/
def ofLiteral {pub : LiteralTranscript.Public} {rs : TranscriptRounds}
    (c : LiteralAcceptanceTerminal.Checks pub rs)
    (closed : HchecksAccumulator.ClosedSum LiteralOpeningView.eK c.data c.queries
      (SelectedChallengeMap.rhoOf c.rho)) : Checks pub rs := {
  decoded := c.decoded,data := c.data,view := c.view
  publicParsed := c.publicParsed,matchingRead := c.matchingRead,openingRead := c.openingRead
  m31 := c.m31,queryBytes := c.queryBytes,state31 := c.state31
  m32 := c.m32,rho := c.rho,state32 := c.state32
  entry31 := c.entry31,entry32 := c.entry32,valid31 := c.valid31,valid32 := c.valid32
  queries := c.queries,queryDecode := c.queryDecode
  writer := (writer_iff _ _).2 c.firstMatch
  backend := (backend_iff _ _ _).2 ⟨
    (LiteralPairingChecks.acceptedPairing_iff_checks rs c.data c.matchingRead).2 c.pairingChecks,closed⟩
  semantic := (semantic_iff c.decoded c.data c.queries c.view c.claim c.polynomials
    c.claimParse c.polynomialParse).2 (by
      have h := c.semanticChecks
      unfold sumcheckChecksZ at h
      exact h.2) }

#print axioms semantic_iff
#print axioms toLiteral_nonempty
#print axioms toLiteral
#print axioms ofLiteral
end AspisR1.OraclePortSelectedConsumerC6
end
