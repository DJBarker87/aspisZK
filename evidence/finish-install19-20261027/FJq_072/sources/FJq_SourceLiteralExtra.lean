import FJq_ExtraLiteralRows
import FJq_LiteralY
import FJq_PhysicalRead
import FJq_SourceRowFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceLiteralExtra
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open FIz_ConcretePack (embed)
theorem value (pre : r1_wire.Prefix) (record : r1_wire.ValidatedRecord)
    (source : r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record))
    (out : Array aspis_core.field.QM31 29#usize)
    (run : AspisS1ExtractedRoundChildren.decodeMain 29#usize record 87#usize=ok (.Ok out))
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr)
    (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows p q tr)=some data) :
    (fun l=>embed (FIp_SemanticValues.decode (FJq_MainCells.cell out l)))=data.Y 3 := by
  obtain ⟨row25,row26,row27,r25,r26,r27,ys⟩:=FJq_LiteralY.reached _ data read
  have literal:=FJq_PhysicalRead.value p q tr aligned 25 (by decide) (by decide) _ row25 r25
  have frame:=FJq_SourceRowFrame.value pre p 25#u8 (by decide) record source records
  change CircleRecordCodec.decode 0 (rowBytes p (25#u8).val)=some row25 at literal
  rw [frame] at literal
  funext l
  rw [ys,SelectedOpeningClaims.Y_extra]
  exact FJq_ExtraLiteralRows.value record row25 literal out run l
#print axioms value
end AspisR1.FJq_SourceLiteralExtra
end
