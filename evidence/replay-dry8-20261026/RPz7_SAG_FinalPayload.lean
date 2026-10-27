import PAln_MatchingFacts
import RPz7_PAln_AlignedRead
import RPz7_PAln_OpeningDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_FinalPayload
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem from_read (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (aligned : Aligned p tr)
    (read : LiteralMatchingData.read (typedRows p q tr) = some d) :
    SelectedFieldSequenceCodec.encodeWide d.f = slice p.wire 8007 2048 := by
  obtain ⟨common,staged,row31,word,gamma,kappa,a0,a1,hcommon,hstaged,last,
    hword,hgamma,hkappa,ha0,ha1,same⟩ := PAln_MatchingFacts.read_success_components _ d read
  obtain ⟨b,c,slot,bytes⟩ := aligned.2.2.2.2 31 (by decide) (by decide)
  have valid := PAln_AlignedRead.payload_valid (words p q) 31 b (by decide) (by decide)
  simp only [LiteralOpeningStages.readAt,typedRows,List.getElem?_mapIdx,slot,
    Option.map_some,Option.bind_some,if_pos valid,restore_erases] at last
  rw [bytes] at last
  have encoded := OpeningRecordCodec.encode_of_decode _ row31 last
  rw [same]
  change SelectedFieldSequenceCodec.encodeWide row31 = _
  have unframed := congrArg (List.drop 4) encoded
  simpa [OpeningRecordCodec.encode,OpeningRecordCodec.encodePayload,
    LengthFrameCodec.frame,PublicInitFrame.lengthBytes_length,rowBytes,
    framed,PAln_RowBounds.le32_length] using unframed

#print axioms from_read
end AspisR1.SAG_FinalPayload
end
