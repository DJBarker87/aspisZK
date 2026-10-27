import FIq_TypedInitial
import PAln_AlignedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceRowFrame
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open OraclePortCompactDraft
/-- The source prefix and physical parsed semantic rows identify the very
same framed record, including row25; no byte identity is postulated. -/
theorem value (pre : r1_wire.Prefix) (p : Parsed) (row : U8) (below : row.val<27)
    (record : r1_wire.ValidatedRecord)
    (read : r1_wire.Prefix.validated_record pre row=ok (.Ok record))
    (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val)) :
    rowBytes p row.val=record.framed.val.map ExtractedRecordByteValue.rawByte := by
  have slot:=(RawActualAnnotatedTypedRows.validated_record_bytes pre row record read).2
  have actual : p.semantic[row.val]?=some (record.framed.val.map ExtractedRecordByteValue.rawByte) := by
    rw [records,List.getElem?_map,slot]
    rfl
  simp only [rowBytes,if_pos below,actual,Option.getD_some]
#print axioms value
end AspisR1.FJq_SourceRowFrame
end
