import F3J_SemanticLog
import PAln_SemanticLayout
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_RowBindings
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation SourceDigestAddresses
open OraclePortCompactDraft MultiproofConeCanonical

theorem empty (b : Bytes) (frame : PAln_SemanticLayout.Frame 0 b) : b=PublicInitFrame.emptyRecord := by
  obtain ⟨payload,size,canonical,same⟩ := frame
  have nil : payload=[] := List.eq_nil_of_length_eq_zero (by simpa [rowShape] using size)
  subst payload
  simpa [rowShape,le32,PublicInitFrame.emptyRecord] using same

theorem first {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (p : Parsed)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (records : p.semantic=pre.records.val.map (fun s => bytesOf s.val))
    (number : c.row.val=0) : rawBytes c.record.framed=PublicInitFrame.emptyRecord := by
  have slot : p.semantic[0]?=some (rawBytes c.record.framed) := by
    rw [records,List.getElem?_map,← number,c.slot]
    rfl
  exact empty _ (by simpa only [Nat.zero_add] using
    PAln_SemanticLayout.at_index 0 p.semantic (PAln_SemanticLayout.layout _ _ _ _ rows) 0 _ slot)

theorem payload {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (p : Parsed)
    (records : p.semantic=pre.records.val.map (fun s => bytesOf s.val))
    (below : c.row.val<27) : rowBytes p c.row.val=rawBytes c.record.framed := by
  simp only [rowBytes,if_pos below,records,List.getElem?_map,c.slot,Option.map_some,Option.getD_some]
  rfl

theorem bound {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (p : Parsed)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (records : p.semantic=pre.records.val.map (fun s => bytesOf s.val)) :
    (rawBytes c.record.framed).length≤SelectedTranscriptParams.D := by
  have slot : p.semantic[c.row.val]?=some (rawBytes c.record.framed) := by
    rw [records,List.getElem?_map,c.slot]
    rfl
  exact PAln_RowBounds.semantic_bound 27 0 _ _ rows _ (List.mem_of_getElem? slot)

#print axioms empty
#print axioms first
#print axioms payload
#print axioms bound
end AspisR1.F3J_RowBindings
end
