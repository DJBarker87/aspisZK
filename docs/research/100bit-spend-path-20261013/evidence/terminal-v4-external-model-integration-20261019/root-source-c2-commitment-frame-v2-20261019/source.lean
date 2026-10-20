import ExtractedSourceDigestAddresses
import RawParsedRecordRowReadback
import R1SemanticPayloadView
import RawByteCollisionTargets
import R1CommitmentRootFrames

/-! Identify the commitment-root target in the actual source row2 digest input.
Uses the strict source accessor/codec view; no independent frame equality or
root-parser premise. Oracle-log membership/cut stability remain separate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawSourceC2CommitmentFrame
open Aeneas Aeneas.Std Result
open AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open SourceDigestAddresses

theorem actual_c2_frame {H : Type} {D : aspis_core.Digest32 H}
    {pre : r1_wire.Prefix} (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (c : SourceFull25.Call D pre) (hrow : c.row.val = 2) :
    TranscriptStep.flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed) =
      CommitmentRootFrames.c2Frame (decodeState c.before.state) (SemanticPayloadView.rootAt2 values) := by
  have hdecoded := RawParsedRecordRowReadback.record_decodes_fixed_row pre values hfull
    ⟨2,by decide⟩ c.row c.record hrow c.validated
  have hroot : values ⟨2,by decide⟩ =
      ⟨SemanticRecordCodec.Payload.c2Root (SemanticPayloadView.rootAt2 values),by rfl⟩ := by
    apply Subtype.ext
    exact SemanticPayloadView.rootAt2_payload values
  rw [hroot] at hdecoded
  have hmap : rawBytes c.record.framed =
      c.record.framed.val.map ExtractedRecordByteValue.rawByte := by
    unfold rawBytes
    apply List.map_congr_left
    intro b hb
    apply Fin.ext
    rfl
  rw [← hmap] at hdecoded
  have hencoded := SemanticRecordCodec.encode_of_decode ⟨2,by decide⟩ _ _ hdecoded
  have htag : decodeByte c.tag = (162 : Byte) := by
    apply Fin.ext
    change c.tag.val = 162
    have ht := c.tag_code
    rw [c.record_row,hrow] at ht
    omega
  rw [flatten_absorb,htag,← hencoded]
  simp only [SemanticRecordCodec.encode,SemanticRecordCodec.payloadTag,
    SemanticRecordCodec.payloadBytes,RecordFrameCodec.frame,RecordFrameCodec.header,
    bytes_length,CommitmentRootFrames.c2Frame,CommitmentRootFrames.c2Prefix,List.append_assoc]
  rfl

theorem actual_c2_target {H : Type} {D : aspis_core.Digest32 H}
    {pre : r1_wire.Prefix} (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (c : SourceFull25.Call D pre) (hrow : c.row.val = 2) :
    RawByteCollisionTargets.pred 8
      (TranscriptStep.flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed)) =
      some (SemanticPayloadView.rootAt2 values) := by
  rw [actual_c2_frame values hfull c hrow]
  exact RawByteCollisionTargets.trailing_frame
    (CommitmentRootFrames.c2Prefix (decodeState c.before.state)) (SemanticPayloadView.rootAt2 values)

theorem full25_has_c2_target {H : Type} {D : aspis_core.Digest32 H}
    {pre : r1_wire.Prefix} (values : SemanticPrefixCodec.Full)
    (hfull : SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre)
    (cs : List (SourceFull25.Call D pre))
    (hrows : cs.map (fun c => c.row.val) = List.range 25) :
    ∃ c ∈ cs, c.row.val = 2 ∧
      TranscriptStep.flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed) =
        CommitmentRootFrames.c2Frame (decodeState c.before.state) (SemanticPayloadView.rootAt2 values) ∧
      RawByteCollisionTargets.pred 8
        (TranscriptStep.flatten (TranscriptStep.absorbParts c.before.state c.tag c.record.framed)) =
        some (SemanticPayloadView.rootAt2 values) := by
  have hmem : 2 ∈ cs.map (fun c => c.row.val) := by
    rw [hrows]
    decide
  obtain ⟨c,hc,hrow⟩ := List.mem_map.mp hmem
  exact ⟨c,hc,hrow,actual_c2_frame values hfull c hrow,actual_c2_target values hfull c hrow⟩

#print axioms actual_c2_frame
#print axioms actual_c2_target
#print axioms full25_has_c2_target
end AspisR1PublicPreparation.RawSourceC2CommitmentFrame
end
