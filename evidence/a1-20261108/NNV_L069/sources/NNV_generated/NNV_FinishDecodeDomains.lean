import NNV_FinishRecordDomain
import NNV_FinishDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishDecodeDomains
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem extra (p : Prefix) (r : Record)
 (called : LIB_VRecordsAll.validatedRecord p 25 = .ok r) : LIB_VDecode.Domain r 87 := by
 have fields := NNV_FinishRecordDomain.returned p 25#u8 (by decide) r called
 constructor
 · rw [fields.1]; exact NGO_CallerDomains.Call.extra
 · rw [fields.1]; exact fields.2

theorem before (p : Prefix) (r : Record)
 (called : LIB_VRecordsAll.validatedRecord p 26 = .ok r) : LIB_VDecode.Domain r 0 := by
 have fields := NNV_FinishRecordDomain.returned p 26#u8 (by decide) r called
 constructor
 · rw [fields.1]; exact NGO_CallerDomains.Call.beforeZ1
 · rw [fields.1]; exact fields.2
#print axioms extra
#print axioms before
end AspisR1.NNV_FinishDecodeDomains
end
