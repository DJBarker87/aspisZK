import FIn_Staged
import RPz7_SAG_FinalPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIn_Payloads
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem decode {A : Type} (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr) (row : Nat) (positive : 0<row) (below : row<33)
    (decoder : Bytes → Option A) (value : A)
    (read : LiteralOpeningStages.readAt (typedRows p q tr) row decoder=some value) :
    decoder (rowBytes p row)=some value := by
  obtain ⟨b,c,slot,bytes⟩ := aligned.2.2.2.2 row positive below
  have valid := PAln_AlignedRead.payload_valid (words p q) row b positive below
  simp only [LiteralOpeningStages.readAt,typedRows,List.getElem?_mapIdx,slot,
    Option.map_some,Option.bind_some,if_pos valid,restore_erases] at read
  rw [bytes] at read
  exact read

theorem first (p : Parsed) (f : OpeningRecordCodec.Payload .first)
    (read : OpeningRecordCodec.decode .first (rowBytes p 29)=some f) :
    SelectedFieldSequenceCodec.encodeWide f = slice p.wire 7527 224 := by
  have encoded := OpeningRecordCodec.encode_of_decode _ f read
  have unframed := congrArg (List.drop 4) encoded
  simpa [OpeningRecordCodec.encode,OpeningRecordCodec.encodePayload,
    LengthFrameCodec.frame,PublicInitFrame.lengthBytes_length,rowBytes,
    framed,PAln_RowBounds.le32_length] using unframed

theorem second (p : Parsed) (f : OpeningRecordCodec.Payload .second)
    (read : OpeningRecordCodec.decode .second (rowBytes p 30)=some f) :
    SelectedFieldSequenceCodec.encodeWide f.2 = slice p.wire 7783 224 := by
  rcases f with ⟨root,coeff⟩
  have encoded := OpeningRecordCodec.encode_of_decode (row := .second) _ (root,coeff) read
  have unframed := congrArg (List.drop 36) encoded
  simpa [OpeningRecordCodec.encode,OpeningRecordCodec.encodePayload,
    LengthFrameCodec.frame,PublicInitFrame.lengthBytes_length,rowBytes,
    framed,PAln_RowBounds.le32_length,OpeningRecordCodec.stateBytes,bytes_length,
    slice,List.drop_append,List.drop_take,List.drop_drop,
    List.drop_eq_nil_of_le] using unframed

theorem from_read (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (aligned : Aligned p tr) (read : LiteralMatchingData.read (typedRows p q tr)=some d) :
    ∃ (f0 f1 : Fin 7 → AspisWideTower.WideExact),
      SelectedFieldSequenceCodec.encodeWide f0 = slice p.wire 7527 224 ∧
      SelectedFieldSequenceCodec.encodeWide f1 = slice p.wire 7783 224 ∧
      d.p0 = OpeningPolynomialView.polynomial f0 ∧ d.p1 = OpeningPolynomialView.polynomial f1 := by
  obtain ⟨common,staged,row31,word,gamma,kappa,a0,a1,hcommon,hstaged,last,
    hword,hgamma,hkappa,ha0,ha1,same⟩ := PAln_MatchingFacts.read_success_components _ d read
  have stages := FIn_Staged.reads _ staged hstaged
  have f0 := first p staged.toFirst.row29 (decode p q tr aligned 29 (by decide) (by decide) _ _ stages.1)
  have f1 := second p staged.row30 (decode p q tr aligned 30 (by decide) (by decide) _ _ stages.2)
  exact ⟨staged.toFirst.row29,staged.row30.2,f0,f1,by rw [same]; rfl,by rw [same]; rfl⟩

#print axioms decode
#print axioms first
#print axioms second
#print axioms from_read
end AspisR1.FIn_Payloads
end
