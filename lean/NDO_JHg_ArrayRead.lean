import NDO_JHg_FieldRead
import RPz7_S6NativeSnapshotReadArrayV1
import NDO_JFt_ExactArray
set_option autoImplicit false
namespace AspisR1.JHg_ArrayRead
open Aeneas Aeneas.Std Result WP
/-- Source array decoder on one symbolic field window. -/
theorem source (data : Slice U8) (off n : Nat) (N : Usize)
    (arr : Array U8 N) (selected : (data.val.drop off).take n=arr.val) :
    AspisS6NativeSnapshotReadArray.read_array N (JHg_FieldRead.segment data off n)=ok arr := by
  have size : (JHg_FieldRead.segment data off n).length=N.val := by
    change ((data.val.drop off).take n).length=N.val
    rw [selected,arr.property]
  obtain ⟨out,call,bytes⟩:=WP.spec_imp_exists
    (AspisS6NativeSnapshotReadArray.read_array_spec N (JHg_FieldRead.segment data off n) size)
  have same : out=arr := Subtype.ext (bytes.trans selected)
  rw [same] at call
  exact call
#print axioms source

theorem cast (data : Slice U8) (off n : Nat) (N : Usize)
    (arr : Array U8 N) (selected : (data.val.drop off).take n=arr.val) :
    core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8
      (JHg_FieldRead.segment data off n)=ok (.Ok arr) :=
  JFt_ExactArray.cast N _ arr selected
#print axioms cast
end AspisR1.JHg_ArrayRead
