import NDO_JFu_PublicRange
set_option autoImplicit false
namespace AspisR1.JHg_FieldRead
open Aeneas Aeneas.Std Result WP
/-- Symbolic native slice operation; the buffer is never normalized. -/
def segment (data : Slice U8) (off count : Nat) : Slice U8 :=
  ⟨(data.val.drop off).take count,by
    have h:=data.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem length (data : Slice U8) (off count : Nat) (bound : off+count≤data.val.length) :
    (segment data off count).val.length=count := by
  simp only [segment,List.length_take,List.length_drop]
  omega
#print axioms length

theorem read (data : Slice U8) (start stop : Usize)
    (order : start.val≤stop.val) (bound : stop.val≤data.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data {start:=start,«end»:=stop}=
      ok (segment data start.val (stop.val-start.val)) := by
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      data {start:=start,«end»:=stop}
      ⦃ out => out=segment data start.val (stop.val-start.val) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [segment,List.slice] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call
#print axioms read
end AspisR1.JHg_FieldRead
