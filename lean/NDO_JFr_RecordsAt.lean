import NDO_JFr_PrefixRecords
set_option autoImplicit false
namespace AspisR1.JFr_RecordsAt
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem source (pre : r1_wire.Prefix) (records : pre.records.val=JFw_Records.frames)
    (row : U8) (bound : row.val<27) (frame : Slice U8)
    (slot : JFw_Records.frames[row.val]?=some frame) :
    r1_wire.Prefix.validated_record pre row=ok (.Ok ⟨row,frame⟩) := by
  obtain ⟨vr,call⟩ := JFv_PrefixRecord.validated pre row bound
  obtain ⟨sameRow,current⟩ := SourceFull25.validated_record_bytes pre row vr call
  change pre.records.val[row.val]?=some vr.framed at current
  rw [records,slot] at current
  have sameFrame : vr.framed=frame := (Option.some.inj current).symm
  have same : vr=(⟨row,frame⟩ : r1_wire.ValidatedRecord) := by
    cases vr with | mk a b =>
      dsimp only at sameRow sameFrame
      cases sameRow
      cases sameFrame
      rfl
  exact same ▸ call

#print axioms source
end AspisR1.JFr_RecordsAt
