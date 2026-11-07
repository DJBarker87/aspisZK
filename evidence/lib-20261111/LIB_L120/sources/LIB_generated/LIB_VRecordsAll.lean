import LIB_VDecode
set_option autoImplicit false
noncomputable section
namespace LIB_VRecordsAll
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1PublicPreparation
abbrev validatedRecord := LIB_VRecords.validatedRecord
abbrev decodeK29 := LIB_VDecode.decodeK29
abbrev payload := LIB_VRecords.payload
abbrev state := LIB_VRecords.state
theorem decode_native (r : Record) (off : Usize)
 (call : NGO_CallerDomains.Call r.row.val (29#usize).val off.val)
 (framed : r.framed.val.length=5+NFU_PacketDomains.payloadSize r.row.val) :
 RawActualDecodeKMainAdapter.decodeMain 29#usize r off =
 .ok (LIB_VRecords.raw ((decodeK29 r off.val).map k29Raw)) := by
 have numbers := NGO_CallerDomains.numeric r.row.val 29 off.val call
 have bound : off.val≤116 := by omega
 have same : LIB_VDecode.offset off.val=off := UScalar.val_eq_imp _ _ (LIB_VDecode.offset_value off.val bound)
 have native := LIB_VDecode.decode_exact r off.val ⟨call,framed⟩
 simpa only [same] using native
theorem payload_native (p : Prefix) (r : U8) :
 (do let out ← FinishModel.payload (prefixRaw p) r
     Result.ok ((LIB_VRecords.host out).map LIB_Carriers.bytes)) =
 .ok (payload p r.val) := by
 rw [(Classical.choose_spec (LIB_VRecords.payload_total p r)),bind_tc_ok]
 rw [LIB_VRecords.payload_exact]
#print axioms decode_native
#print axioms payload_native
end LIB_VRecordsAll
