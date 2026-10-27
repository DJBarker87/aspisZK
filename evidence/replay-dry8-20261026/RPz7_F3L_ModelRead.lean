import RPz7_F3L_SamplerAligned
import RPz7_F3L_OrdinaryReads
import RPz7_PAln_DataRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_ModelRead
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

theorem read (H : Bytes → State) (p : Parsed) (root : State)
    (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (pub : LiteralTranscript.Public) (q : Fin 22 → Fin 262144)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (header : OraclePortHeader.accepts p.wire=true) (canonical : scan p.wire)
    (typed : ∃ decoded,SemanticPrefixCodec.decodeFrom 0 (p.semantic.take 25)=some decoded)
    (tag : pub.tag=p.wire[8]?.getD 0)
    (parsedPublic : ∃ decoded,SemanticPublicWire.parsePublic pub.pubBytes=some decoded)
    (rootBytes : bytes root=root0 p) :
    let tr := LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program
      (F3J_InputRows.proof p root w bound) 0 33 (FS.emptyPrefix pub))).2
    Aligned p tr ∧ OraclePortStoredParserC4.parseReached p.wire tr=some p ∧
      ∃ d,LiteralMatchingData.read (typedRows p q tr)=some d := by
  have aligned := F3L_SamplerAligned.aligned H p root w bound pub tag parsedPublic rootBytes
  exact ⟨aligned,OraclePortStoredParserC4.parse_of_parts p.wire p.semantic _ header canonical rows aligned,
    PAln_DataRead.exists_read p q _ aligned rows ((OraclePortHeader.accepts_iff _).mp header).1
      canonical typed (fun row below=>F3L_OrdinaryReads.read H p root w bound pub q row below)⟩

#print axioms read
end AspisR1.F3L_ModelRead
end
