import NNV_FinishCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishRecord
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem returned (p : Prefix) (row : U8) (record : Record)
 (called : LIB_VRecordsAll.validatedRecord p row.val = .ok record) :
 r1_wire.Prefix.validated_record (prefixRaw p) row = .ok (.Ok record) := by
 change LIB_VRecords.validatedRecord p row.val = .ok record at called
 rw [LIB_VRecords.validated_exact,called]
 rfl
#print axioms returned
end AspisR1.NNV_FinishRecord
end
