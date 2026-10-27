import JHg_AuditRegistry
import JHg_ArrayRead
set_option autoImplicit false
namespace AspisR1.JHg_Scalar19
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_DataRegistry.value
def value : Array U8 8#usize := Array.make 8#usize [1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem bytes : (JHg_FieldRead.segment JHb_DataRegistry.value 104 8).val=value.val := by
  unfold JHg_FieldRead.segment JHb_DataRegistry.value
  change (JHb_DataRegistry.bytes.drop 104).take 8=value.val
  rw [JHg_AuditRegistry.generation];rfl
#print axioms bytes
theorem cast : core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8
    (JHg_FieldRead.segment JHb_DataRegistry.value 104 8)=ok (.Ok value) :=
  JHg_ArrayRead.cast _ 104 8 8#usize value bytes
#print axioms cast
theorem native : core.num.U64.from_le_bytes value=1#u64 := rfl
#print axioms native
end AspisR1.JHg_Scalar19
