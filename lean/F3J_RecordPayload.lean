import F3J_RowBindings
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_RecordPayload
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft MultiproofConeCanonical SourceDigestAddresses

theorem row_bytes (pre : r1_wire.Prefix) (record : r1_wire.ValidatedRecord) (row : U8)
    (p : Parsed) (records : p.semantic=pre.records.val.map (fun s => bytesOf s.val))
    (below : row.val<27) (read : r1_wire.Prefix.validated_record pre row=ok (.Ok record)) :
    rowBytes p row.val=rawBytes record.framed := by
  obtain ⟨number,slot⟩ := SourceFull25.validated_record_bytes pre row record read
  simp only [rowBytes,if_pos below,records,List.getElem?_map,slot,Option.map_some,Option.getD_some]
  rfl

#print axioms row_bytes
end AspisR1.F3J_RecordPayload
end
