import OraclePortMatchingRewordC6
import OraclePortSelectedConsumerC6

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace AspisR1.OraclePortObservationTransportC6
open LiteralAcceptanceTerminal
open OraclePortReaderPlumbingC6 OraclePortSelectedArithmeticC4 OraclePortSelectedObservationsC6
open AspisPool.AlgorithmicCircleDecoderV7
attribute [local irreducible] MatchingSupport.match0 MatchingSupport.AcceptedPairing
  QueryResidualBridge.values QueryResidualBridge.basis HchecksAccumulator.ClosedSum
  LiteralTypedWords.word OraclePortSelectedConsumerC6.Semantic

/-- Extract observation checks directly from typed acceptance and the late
reader fields, without first identifying candidate rows with compiler rows. -/
theorem ofTyped (pub : LiteralTranscript.Public) (rs : TranscriptRounds)
    (i : RecordedBinaryExperimentBin.SourceInputs) (q : Fin 22 → Fin 262144)
    (publicParsed : SemanticPublicWire.parsePublic pub.pubBytes = some i.decoded)
    (row31 : rs[31]? = some (i.m31,(TranscriptView.Value.queries (.ok i.queryBytes),i.state31)))
    (row32 : rs[32]? = some (i.m32,(TranscriptView.Value.ordinary i.rho,i.state32)))
    (valid31 : LiteralTranscript.valid 31 i.m31) (valid32 : LiteralTranscript.valid 32 i.m32)
    (decoded : LiteralQueryRead.decode i.queryBytes = some q)
    (accepted : D0TypedChecks.verify rs i = true) :
    Nonempty (OraclePortSelectedConsumerC6.Checks pub rs) := by
  have matching := D0TypedChecks.accepted_matching rs i accepted
  obtain ⟨v,claim,polys,hopen,hclaim,hpolys⟩ :=
    HchecksReaderComposition.matching_read_parsers rs i.data matching
  have localChecks := typed_accepted rs i q decoded accepted
  have equations := (D0TypedChecks.accepted_components rs i accepted).2.2.2.1
  exact ⟨{
    decoded := i.decoded,data := i.data,view := v
    publicParsed := publicParsed,matchingRead := matching,openingRead := hopen
    m31 := i.m31,queryBytes := i.queryBytes,state31 := i.state31
    m32 := i.m32,rho := i.rho,state32 := i.state32
    entry31 := row31,entry32 := row32,valid31 := valid31,valid32 := valid32
    queries := q,queryDecode := decoded,writer := localChecks.1,backend := localChecks.2
    semantic := (OraclePortSelectedConsumerC6.semantic_iff i.decoded i.data q v claim polys hclaim hpolys).2
      (equations v claim polys hopen hclaim hpolys) }⟩

/-- Every consumer check transfers to recovered compiler words from selected
fibre agreement. The full rows need not equal the candidate rows. -/
theorem transport (pub : LiteralTranscript.Public) (rs : TranscriptRounds)
    (c : OraclePortSelectedConsumerC6.Checks pub rs) (w : CanonicalCutEnrichedTranscript.Words)
    (initial : ∀ j lane, FirstFold.fibre (c.data.W lane) (c.queries j) =
      FirstFold.fibre ((LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK w.c1 w.c2) lane)
        (c.queries j))
    (opened : ∀ j, c.data.V (c.queries j) = w.final (c.queries j))
    (folded : ∀ j slot, c.data.V (childIndex (n := 65536) (parentIndex (n := 65536) (c.queries j)) slot) =
      w.final (childIndex (n := 65536) (parentIndex (n := 65536) (c.queries j)) slot)) :
    Nonempty (OraclePortSelectedConsumerC6.Checks pub (reword w rs)) := by
  let d := withWords c.data
    (LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK w.c1 w.c2) w.final
  have matching : LiteralMatchingData.read (reword w rs) = some d :=
    OraclePortMatchingRewordC6.matching w rs c.data c.matchingRead
  obtain ⟨v,hopen,_,_,_,_,_⟩ := OraclePortOpeningRewordC6.opening w rs c.view c.openingRead
  have semantic := OraclePortMatchingRewordC6.semantic w rs c.view v c.openingRead hopen
  have same : observe c.data c.queries = observe d c.queries :=
    observe_withWords c.data _ w.final c.queries initial opened folded
  have late31 : CanonicalCutEnrichedTranscript.enrichMessage w c.m31 = c.m31 :=
    D0InstanceAdmission.valid_payload_injective 31 (by decide) (by decide) (by decide) _ _
      ((OraclePortSemanticObservationsC6.valid_enrich w 31 c.m31).2 c.valid31) c.valid31 (erased w c.m31)
  have late32 : CanonicalCutEnrichedTranscript.enrichMessage w c.m32 = c.m32 :=
    D0InstanceAdmission.valid_payload_injective 32 (by decide) (by decide) (by decide) _ _
      ((OraclePortSemanticObservationsC6.valid_enrich w 32 c.m32).2 c.valid32) c.valid32 (erased w c.m32)
  have row31 : (reword w rs)[31]? = some (c.m31,(TranscriptView.Value.queries (.ok c.queryBytes),c.state31)) := by
    simp only [reword,List.getElem?_map,c.entry31,Option.map_some,late31]
  have row32 : (reword w rs)[32]? = some (c.m32,(TranscriptView.Value.ordinary c.rho,c.state32)) := by
    simp only [reword,List.getElem?_map,c.entry32,Option.map_some,late32]
  exact ⟨{
    decoded := c.decoded,data := d,view := v
    publicParsed := c.publicParsed,matchingRead := matching,openingRead := hopen
    m31 := c.m31,queryBytes := c.queryBytes,state31 := c.state31
    m32 := c.m32,rho := c.rho,state32 := c.state32
    entry31 := row31,entry32 := row32,valid31 := c.valid31,valid32 := c.valid32
    queries := c.queries,queryDecode := c.queryDecode
    writer := same ▸ c.writer,backend := same ▸ c.backend
    semantic := by rw [← same,semantic]; exact c.semantic }⟩

#print axioms ofTyped
#print axioms transport
end AspisR1.OraclePortObservationTransportC6
end
