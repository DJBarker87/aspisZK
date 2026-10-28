import NDO_JFt_Range
import RPz7_S6NativeSnapshotReadArrayV1
set_option autoImplicit false
namespace AspisR1.JFt_ReadArray
open Aeneas Aeneas.Std Result WP

theorem source (off n : Nat) (bound : off+n≤1880) (N : Usize)
    (arr : Array U8 N) (selected : (JFx_NativeBytes.publicInput.val.drop off).take n=arr.val) :
    AspisS6NativeSnapshotReadArray.read_array N (JFu_PublicRange.segment off n bound)=ok arr := by
  have size : (JFu_PublicRange.segment off n bound).length=N.val := by
    change ((JFx_NativeBytes.publicInput.val.drop off).take n).length=N.val
    rw [selected,arr.property]
  obtain ⟨out,call,bytes⟩:=WP.spec_imp_exists
    (AspisS6NativeSnapshotReadArray.read_array_spec N (JFu_PublicRange.segment off n bound) size)
  have same : out=arr := Subtype.ext (bytes.trans selected)
  rw [same] at call
  exact call

#print axioms source
end AspisR1.JFt_ReadArray
