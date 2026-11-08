import NNV_FinishRecord
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishRecordDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (p : Prefix) (row : U8) (live : row.val < 27) (record : Record)
 (called : LIB_VRecordsAll.validatedRecord p row.val = .ok record) :
 record.row = row ∧ record.framed.val.length = 5+NFU_PacketDomains.payloadSize row.val := by
 obtain ⟨other,hr,tag,frame⟩ := NIX_ProducerInstall.framed p.source p.parsed p.parse_eq row live
 have same : other = record := core.result.Result.Ok.inj (Result.ok.inj
  (hr.symm.trans (NNV_FinishRecord.returned p row record called)))
 subst other
 exact ⟨tag,frame⟩
#print axioms returned
end AspisR1.NNV_FinishRecordDomain
end
