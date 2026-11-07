import NNG_LIBRecordFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_GetterReturn136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport

theorem returned (p : LIB_VCarriers.Prefix) (row : U8) (rec : LIB_VCarriers.Record)
    (field : LIB_VRecords.validatedRecord p row.val = .ok rec) :
    NNG_Install.validatedRecord (NNG_LIBData.lowerPrefix p) row = .ok (.Ok (fromT14 rec)) := by
  unfold NNG_Install.validatedRecord NNG_LIBData.lowerPrefix
  rw [fromT12_inverse,LIB_VRecords.validated_exact,field]
  rfl
#print axioms returned
end AspisR1.NNG_GetterReturn136
