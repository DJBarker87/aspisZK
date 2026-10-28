import JHg_AuditLane
import NDO_JHg_ArrayRead
set_option autoImplicit false
namespace AspisR1.JHg_Scalar18
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataLane.value
def value : Array U8 8#usize := Array.make 8#usize [13#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem bytes : (JHg_FieldRead.segment JHb_DataLane.value 88 8).val=value.val := by
  unfold JHg_FieldRead.segment JHb_DataLane.value
  change (JHb_DataLane.bytes.drop 88).take 8=value.val
  rw [JHg_AuditLane.next_index];rfl
#print axioms bytes
theorem cast : core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
    (JHg_FieldRead.segment JHb_DataLane.value 88 8)=ok (.Ok value) :=
  JHg_ArrayRead.cast _ 88 8 8#usize value bytes
#print axioms cast
theorem native : core.num.U64.from_le_bytes value=13#u64 := rfl
#print axioms native
end AspisR1.JHg_Scalar18
