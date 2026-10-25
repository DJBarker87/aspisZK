import PAln_ChallengeRows
import PAln_DataRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_Carrier
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

/-- Fixed33-row carrier, retaining exact source semantic challenges and the
provided suffix values. Source binding of those suffix/public inputs remains
separate; this constructor asserts no accepted-source refinement. -/
def make {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (p : Parsed) (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (header : OraclePortHeader.accepts p.wire=true)
    (pub : LiteralTranscript.Public) (root : State) (cs : List (SourceFull25.Call D pre))
    (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
    (queries : List Nat) (rho : LiteralTranscript.E) : ErasedPrefix :=
  PAln_Transcript.transcript p pub root
    (fun row => PAln_RowBounds.row_bound p rows ((OraclePortHeader.accepts_iff _).mp header).1 row)
    (PAln_ChallengeRows.atRow cs values states queries rho)

theorem ordinary {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (p : Parsed) (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (header : OraclePortHeader.accepts p.wire=true)
    (pub : LiteralTranscript.Public) (root : State) (cs : List (SourceFull25.Call D pre))
    (count : cs.length=25) (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
    (queries : List Nat) (rho : LiteralTranscript.E) (q : Fin 22 → Fin 262144) :
    ∀ i,i<31 → ∃ value,LiteralChallengeRead.ordinaryAt
      (typedRows p q (make p rows header pub root cs values states queries rho)) i=some value := by
  intro i below
  obtain ⟨value,shape⟩ := PAln_ChallengeRows.ordinary cs count values states queries rho i below
  refine ⟨value,?_⟩
  unfold make LiteralChallengeRead.ordinaryAt
  rw [PAln_TypedRows.entry _ _ _ _ _ _ i (by omega)]
  simp only [Option.bind_some,shape]

theorem parser_and_data {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (p : Parsed) (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (header : OraclePortHeader.accepts p.wire=true) (scan : scan p.wire)
    (typed : ∃ decoded,SemanticPrefixCodec.decodeFrom 0 (p.semantic.take 25)=some decoded)
    (pub : LiteralTranscript.Public) (root : State) (cs : List (SourceFull25.Call D pre))
    (count : cs.length=25) (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
    (queries : List Nat) (rho : LiteralTranscript.E) (q : Fin 22 → Fin 262144)
    (tag : pub.tag=p.wire[8]?.getD 0)
    (publicParsed : ∃ decoded,SemanticPublicWire.parsePublic pub.pubBytes=some decoded)
    (initial : bytes root=root0 p) :
    let tr := make p rows header pub root cs values states queries rho
    Aligned p tr ∧ OraclePortStoredParserC4.parseReached p.wire tr=some p ∧
      ∃ data,LiteralMatchingData.read (typedRows p q tr)=some data := by
  dsimp only
  have aligned := PAln_Transcript.aligned p pub root _
    (PAln_ChallengeRows.atRow cs values states queries rho) tag publicParsed initial
  refine ⟨aligned,?_,?_⟩
  · exact OraclePortStoredParserC4.parse_of_parts p.wire p.semantic _ header scan rows aligned
  · exact PAln_DataRead.exists_read p q _ aligned rows
      ((OraclePortHeader.accepts_iff _).mp header).1 scan typed
      (ordinary p rows header pub root cs count values states queries rho q)

#print axioms ordinary
#print axioms parser_and_data
end AspisR1.PAln_Carrier
end
