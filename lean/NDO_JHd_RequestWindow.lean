import JHb_RequestCarrier
import NDO_JFs_ArrayWindow
set_option autoImplicit false
namespace AspisR1.JHd_RequestWindow
open Aeneas Aeneas.Std Result WP

def value : Array U8 320#usize := ⟨JHb_DataRequest.bytes,JHb_DataRequest.length⟩
def window (off n : Nat) (bound : off+n≤320) : Slice U8 :=
  ⟨(JHb_DataRequest.bytes.drop off).take n,by
    have h : ((JHb_DataRequest.bytes.drop off).take n).length≤320 := by
      rw [List.length_take,List.length_drop,JHb_DataRequest.length]
      omega
    scalar_tac⟩

theorem length (off n : Nat) (bound : off+n≤320) :
    (window off n bound).val.length=n := by
  simp only [window,List.length_take,List.length_drop,JHb_DataRequest.length]
  omega
#print axioms length

theorem range (start stop : Usize) (order : start.val≤stop.val) (inside : stop.val≤320) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      value {start:=start,«end»:=stop}=
      ok (window start.val (stop.val-start.val) (by omega)) := by
  have size : value.val.length=320 := JHb_DataRequest.length
  have spec : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      value {start:=start,«end»:=stop}
      ⦃ out => out=window start.val (stop.val-start.val) (by omega) ⦄ := by
    unfold core.array.Array.index core.ops.index.IndexSlice core.slice.index.Slice.index
    step*
    all_goals try (change stop.val ≤ value.val.length; omega)
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,window,value,Array.to_slice] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call
#print axioms range
end AspisR1.JHd_RequestWindow
