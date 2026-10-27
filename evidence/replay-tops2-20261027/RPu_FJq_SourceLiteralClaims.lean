import RPu_FJq_ClaimsLiteralRows
import RPu_FJq_LiteralY
import RPu_FJq_PhysicalRead
import RPu_FJq_SourceRowFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_SourceLiteralClaims
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open FIz_ConcretePack (embed)
/-- All actual Claims decoder values transported to the literal matching
reader's SAME Y rows, using original record bytes and aligned physical reads. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (pre : r1_wire.Prefix)
    (claims : ClaimsUnrolledFinish.MainClaims)
    (run : ClaimsUnrolledFinish.reference std pre=ok (.Ok claims))
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr)
    (records : p.semantic=pre.records.val.map (fun s=>MultiproofConeCanonical.bytesOf s.val))
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows p q tr)=some data) :
    (fun j l=>embed (FJn_MainClaims.claims claims j l))=
      fun j l=>data.Y ⟨j.val,by omega⟩ l := by
  obtain ⟨record,a,b,c,source,rest⟩:=FJq_ReferenceMain.reached std pre claims run
  obtain ⟨row25,row26,row27,r25,r26,r27,ys⟩:=FJq_LiteralY.reached _ data read
  have literal:=FJq_PhysicalRead.value p q tr aligned 25 (by decide) (by decide) _ row25 r25
  have frame:=FJq_SourceRowFrame.value pre p 25#u8 (by decide) record source records
  change CircleRecordCodec.decode 0 (rowBytes p (25#u8).val)=some row25 at literal
  rw [frame] at literal
  have values:=FJq_ClaimsLiteralRows.value std pre claims run record source row25 literal
  funext j l
  rw [ys,SelectedOpeningClaims.Y_point]
  exact values j l
#print axioms value
end AspisR1.FJq_SourceLiteralClaims
end
