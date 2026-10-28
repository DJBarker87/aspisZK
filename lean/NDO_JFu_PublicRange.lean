import NDO_JFu_PublicHeader
set_option autoImplicit false
namespace AspisR1.JFu_PublicRange
open Aeneas Aeneas.Std Result WP

def segment (off n : Nat) (bound : off+n≤1880) : Slice U8 :=
  ⟨(JFx_NativeBytes.publicInput.val.drop off).take n,by
    have h:=JFx_NativeBytes.publicInput.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem length (off n : Nat) (bound : off+n≤1880) : (segment off n bound).length=n := by
  simp only [segment,Slice.length,List.length_take,List.length_drop,JFx_NativeBytes.publicBytes_length]
  have h : JFx_NativeBytes.publicInput.val.length=1880 := JFx_NativeBytes.publicBytes_length
  simp only [h]
  omega

theorem nested {A : Type} (xs : List A) (off n start count : Nat) (bound : start+count≤n) :
    (((xs.drop off).take n).drop start).take count=(xs.drop (off+start)).take count := by
  simp only [List.drop_take,List.drop_drop,List.take_take]
  rw [Nat.min_eq_left (by omega : count≤n-start)]

theorem read (start stop : Usize) (order : start.val≤stop.val) (bound : stop.val≤1880) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.publicInput {start:=start,«end»:=stop}=
      ok (segment start.val (stop.val-start.val) (by omega)) := by
  have size : JFx_NativeBytes.publicInput.val.length=1880 := JFx_NativeBytes.publicBytes_length
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      JFx_NativeBytes.publicInput {start:=start,«end»:=stop}
      ⦃ out => out=segment start.val (stop.val-start.val) (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [segment,List.slice] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

def snapshot := segment 176 800 (by decide)
def afterstate := segment 976 688 (by decide)
def late := segment 144 1520 (by decide)
def payment := segment 1664 216 (by decide)

#print axioms length
#print axioms nested
#print axioms read
end AspisR1.JFu_PublicRange
