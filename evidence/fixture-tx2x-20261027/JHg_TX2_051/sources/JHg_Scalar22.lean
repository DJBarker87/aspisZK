import JHg_AuditEntry
import JHg_ArrayRead
set_option autoImplicit false
namespace AspisR1.JHg_Scalar22
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataEntry.value
def value : Array U8 8#usize := Array.make 8#usize [255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8,255#u8]
theorem bytes : (JHg_FieldRead.segment JHb_DataEntry.value 272 8).val=value.val := by
  unfold JHg_FieldRead.segment JHb_DataEntry.value
  change (JHb_DataEntry.bytes.drop 272).take 8=value.val
  rw [JHg_AuditEntry.retirement];rfl
#print axioms bytes
theorem cast : core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
    (JHg_FieldRead.segment JHb_DataEntry.value 272 8)=ok (.Ok value) :=
  JHg_ArrayRead.cast _ 272 8 8#usize value bytes
#print axioms cast
theorem native : core.num.U64.from_le_bytes value=18446744073709551615#u64 := rfl
#print axioms native
end AspisR1.JHg_Scalar22
